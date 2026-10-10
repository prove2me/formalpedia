-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedOriginalSample_jointResidueOutput_eq_congruence
-- name    : OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_jointResidueOutput_eq_congruence
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T00:47:50.579307+00:00
-- url     : https://prove2.me/theorems/fb2f0739-cc54-4dba-a58b-09cb969dcb05
-- title:
--   The joint residue output at an original sample equals the forecast congruence output
-- statement:
--   Fix $m \in \mathbb N$, a finite type $G$, a type $X$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), types $E_j$, $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Write $\mathcal V$ for `LayerSamplerVariables G I n B`, short for the predicate `allocatedShortAxis U basis S.value` on `LayerSamplerAxis I n`, and sides for `allocatedPrincipalSides B U basis S`. Let sample be in `CoefficientSamplerArrays I n` over $\mathcal V$ (for each $j$, a real array on $I_j$ and an integer array on $\mathrm{Fin}(n_j)$, indexed by bounded exponents), $\mathrm{base} : X \to \mathbb Z$, $\mathrm{noise} : \mathrm{Option}\,\mathcal V \times X \to \mathbb Z$, $\mathrm{deck}_j :$ `BoundedCoefficientExponent 𝒱 (j+1)` $\to E_j \to \mathbb Z$, $q \in \mathbb N$, $x : G \to$ `IntegerScalarCubeBox Empty S.value`, and $y \in$ `PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides`. Then the function
--   `allocatedJointResidueOutput B U basis S base noise deck (allocatedOriginalSampleCongruenceProjection B U basis S sample) q (g ↦ x g none mod q) (principalResidueLabel q y)`
--   (a map from `Sigma (AllocatedCongruenceRankOutput X E short)` to $\mathbb Z/q$, evaluating OpenAI's forecast polynomials mod $q$) equals the function sending $o$ to the reduction mod $q$ of
--   `forecastCongruenceOutput short (base + integerPhysicalSite root noise) (j ↦ Sum.elim (μ_j).2 (allocatedOriginalSampleDeckValue B U basis S deck x y j)) o`,
--   where $\mathrm{root} =$ `allocatedPhysicalCubeRoot B U basis S 0 x y`, `integerPhysicalSite root noise` is $i \mapsto \mathrm{noise}(\mathrm{none}, i) + \sum_k \mathrm{root}(k)\,\mathrm{noise}(\mathrm{some}\,k, i)$, and $\mu_j =$ `allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j` $\in \mathbb R^{I_j} \times \mathbb Z^{\mathrm{Fin}(n_j)}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedOriginalSample_jointResidueOutput_eq_congruence` in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleCongruenceOutput.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B144`, `OAIErdos3B160` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedOriginalSampleCongruenceOutput.lean#L66

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B171
import Definitions.Def_OAIErdos3B173

namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical
open BooleanCubeKernel

variable {m : ℕ} {G X : Type*} [Fintype G]
variable {I E : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)

local notation "short" => allocatedShortAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S

theorem allocatedOriginalSample_jointResidueOutput_eq_congruence
    (sample : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n)
    (base : X → ℤ) (noise : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (deck : ∀ j : Fin m,
      BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1) → E j → ℤ)
    (q : ℕ) (x : G → IntegerScalarCubeBox Empty S.value)
    (y : PrincipalIntegerTuples B (layerSamplerDegree I n) Empty sides) :
    allocatedJointResidueOutput B U basis S base noise deck
      (allocatedOriginalSampleCongruenceProjection B U basis S sample) q
      (fun g => ((x g none : ℤ) : ZMod q)) (principalResidueLabel q y) =
      fun o => (forecastCongruenceOutput (R := ℤ) short
        (base + integerPhysicalSite (allocatedPhysicalCubeRoot B U basis S (fun _ => 0) x y) noise)
        (fun j => Sum.elim
          (allocatedOriginalSamplePhysicalMixedValue B U basis S sample x y j).2
          (allocatedOriginalSampleDeckValue B U basis S deck x y j)) o : ZMod q) := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
