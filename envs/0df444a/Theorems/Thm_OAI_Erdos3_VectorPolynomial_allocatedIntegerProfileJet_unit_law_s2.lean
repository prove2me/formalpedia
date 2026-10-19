-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedIntegerProfileJet_unit_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileJet_unit_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:07:28.121974+00:00
-- url     : https://prove2.me/theorems/49681ad7-36a9-44e0-853c-2d645cf9d9d7
-- title:
--   The unit coefficient source pushed through the normalized profile jet of an integer axis has the allocated integer kernel density
-- statement:
--   Let $m$ be a natural number, $G$ a finite type, $I_j$ ($j \in \operatorname{Fin} m$) finite types, $n : \operatorname{Fin} m \to \mathbb{N}$, and $B$ an assignment of a finite type to each axis of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$; the degree of $(j, \cdot)$ is $j+1$). Let $J_j$ be finite types, $U_j$ a real subspace of $J_j \to \mathbb{R}$, $\mathrm{basis}_j$ a real basis indexed by $\operatorname{Fin} n_j$ of the orthogonal complement of `euclideanSubspace (U j)` (the subspace $U_j$ viewed inside $\mathbb{R}^{J_j}$), $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (OpenAI's structure with a positive natural number `S.value`). Let $\alpha$ and $O$ be finite types with decidable equality, $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\operatorname{Option} \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$), $u$ a principal axis tuple on the grid axes (an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)`, where `allocatedGridAxis` is OpenAI's predicate selecting grid axes), and $\mathrm{rows} : O \to \operatorname{Finset} \alpha$. (All named objects are defined by OpenAI.)
--
--   Let $j \in \operatorname{Fin} m$ and $i \in \operatorname{Fin} n_j$, let $s$ be an embedding of $O$ into `BoundedIntegerExponent G (j+1)` (exponent vectors on $G$ of total degree at most $j+1$) such that the square submatrix, on the columns $s$, of the integer matrix `scalarKernelIntegerJet x (j+1) rows` (rows indexed by $O$, columns by exponents of degree at most $j+1$) has nonzero determinant, assume $\sigma_j \le 1$, and let $y$ be a real-valued function on `PrincipalAxisParameter (fun a => ¬ grid a)` (the joint block parameters of the non-grid axes). Let $\mu$ = `unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, inr i⟩)`, the measure on real functions $r$ of the coefficient slots of the axis $(j, \mathrm{inr}\ i)$ with density $r \mapsto \prod \psi(r_e)$ with respect to Lebesgue measure, $\psi$ being OpenAI's smooth probability profile. Then the pushforward of $\mu$ under the map $r \mapsto$ `allocatedNormalizedProfileJet B U basis S x u rows ⟨j, inr i⟩ y r` (a function $O \to \mathbb{R}$: the Boolean coefficients, on the row sets $\mathrm{rows}(o)$, of OpenAI's axis profile polynomial with coefficients $r$ evaluated at the normalized cube tuple determined by $x$, $u$ and $y$) equals the measure on $O \to \mathbb{R}$ with density `allocatedIntegerKernelDensity B U basis S j i x u rows s hA y` with respect to Lebesgue measure (OpenAI's affine selected jet density for the pivot given by $s$). Here a measure with density $f$ means `withDensity` of $\operatorname{ofReal} \circ f$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileJet_unit_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileJet_unit_law` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean`); the definitions it uses are in the definitions bundles `OAIE3v2B125`, `OAIE3v2B126` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedIntegerProfileJet_unit_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B125
import Definitions.Def_OAIE3v2B126

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped NNReal Classical

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α O : Type*} [Fintype α] [DecidableEq α] [Fintype O] [DecidableEq O]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U basis S.value)
  (allocatedPrincipalSides B U basis S))
variable (rows : O → Finset α)

local notation "grid" => allocatedGridAxis (I := I) U basis S.value
local notation "sides" => allocatedPrincipalSides B U basis S
local notation "input" => partitionedPrincipalInput grid (fun g a => (g, a))
local notation "fixedReal" => Sum.elim
  (fun ga : G × Option α => ((x (Prod.fst ga) (Prod.snd ga) : ℤ) : ℝ) / (S.value : ℝ))
  (principalTupleNormalized (principalAxisLength grid sides) u)

include hR hσ in
theorem allocatedIntegerProfileJet_unit_law_s2 (j : Fin m) (i : Fin (n j))
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inr i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inr i⟩ y) =
      realDensityMeasure volume (allocatedIntegerKernelDensity B U basis S j i x u rows s hA y) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
