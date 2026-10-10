-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedFixedPathKernelFrame_geometry
-- name    : OAI.Erdos3.VectorPolynomial.allocatedFixedPathKernelFrame_geometry
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-10T03:16:21.400758+00:00
-- url     : https://prove2.me/theorems/a73db217-032c-43bd-93e2-ee7948c4db46
-- title:
--   Root budget bounds and unit bound for the fixed-path kernel frame
-- statement:
--   Fix $m \in \mathbb N$, finite types $G$ and $X$, finite types $I_j$ ($j \in \mathrm{Fin}\,m$), $n : \mathrm{Fin}\,m \to \mathbb N$, finite types $B_a$ indexed by $a \in$ `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$), finite types $J_j$ with subspaces $U_j \le \mathbb R^{J_j}$, bases $\mathrm{basis}_j$ (indexed by $\mathrm{Fin}(n_j)$) of the orthogonal complement of `euclideanSubspace (U j)`, reals $R_j, \sigma_j$, and a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities). Let $W =$ `allocatedPhysicalRootBudget B U basis S 0` (a real number, defined as $\sum_k |c_k| + |$`LayerSamplerVariables G I n B`$| \cdot S.\mathrm{value}$ with here $c = 0$). Let $\tau, \xi > 0$ be reals, $\mathrm{box} : X \to \mathbb N$ with $\mathrm{box}(x) > 0$ for all $x$, and let $\mathrm{integerFrame} : \mathrm{Option}($`LayerSamplerVariables G I n B`$) \times X \to \mathbb Z$ belong to the finite set `rectangularWeightIndices 0 (narrowTrimmedSpatialWidths W τ ξ box) 1` (with $G$ and `PrincipalTupleIndex B (layerSamplerDegree I n)` as type parameters of `narrowTrimmedSpatialWidths`). Then $0 \le W$, $0 \le S.\mathrm{value}$, $|G| \cdot S.\mathrm{value} \le W$, and for every $a \in \mathrm{Option}\,G \times X$, $|$`allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a`$| \le 1$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedFixedPathKernelFrame_geometry` in `lean/OAI/Combinatorics/Progressions/Linear/AllocatedFixedPathKernelFrameBounds.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B167` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Linear/AllocatedFixedPathKernelFrameBounds.lean#L45

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B167

namespace OAI

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped Classical

variable {m : ℕ} {G X : Type*} [Fintype G] [Fintype X]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
local notation "budget" => allocatedPhysicalRootBudget B U basis S (fun _ => 0)
local notation "FullInput" => PrincipalTupleIndex B (layerSamplerDegree I n)

theorem allocatedFixedPathKernelFrame_geometry
    {τ ξ : ℝ} (hτ : 0 < τ) (hξ : 0 < ξ)
    (box : X → ℕ) (hbox : ∀ x, 0 < box x)
    (integerFrame : Option (LayerSamplerVariables G I n B) × X → ℤ)
    (hframe : integerFrame ∈ rectangularWeightIndices 0
      (narrowTrimmedSpatialWidths (G := G) (J := FullInput) budget τ ξ box) 1) :
    0 ≤ budget ∧ 0 ≤ (S.value : ℝ) ∧
      (Fintype.card G : ℝ) * (S.value : ℝ) ≤ budget ∧
      ∀ a, |allocatedFixedPathKernelFrame B U basis S τ ξ box integerFrame a| ≤ 1 := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
