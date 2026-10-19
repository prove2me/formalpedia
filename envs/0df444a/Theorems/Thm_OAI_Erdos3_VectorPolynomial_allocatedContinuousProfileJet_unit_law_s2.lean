-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedContinuousProfileJet_unit_law_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileJet_unit_law_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-17T11:43:02.701545+00:00
-- url     : https://prove2.me/theorems/f4598832-a216-4c7f-a8e1-34862dd260a8
-- title:
--   The image of the unit coefficient source under the allocated normalized profile jet has the allocated continuous kernel density
-- statement:
--   **Setting.** Let $m$ be a natural number, $G$ a finite type, $I : \mathrm{Fin}\ m \to \mathrm{Type}$ a family of finite types, $n : \mathrm{Fin}\ m \to \mathbb{N}$, $B$ a family of finite types indexed by `LayerSamplerAxis I n` $= \Sigma_{j}\, (I\ j \oplus \mathrm{Fin}\ (n\ j))$, $J$ a family of finite types indexed by $\mathrm{Fin}\ m$, $U_j$ a real subspace of $J_j \to \mathbb{R}$, and $\mathrm{basis}_j$ a basis indexed by $\mathrm{Fin}\ (n\ j)$ of the orthogonal complement of `euclideanSubspace (U j)`. Let $R, \sigma : \mathrm{Fin}\ m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and $S$ a `LayerSamplerScale B U basis R σ` (defined by OpenAI, with positive natural number `S.value`). Let $\alpha$ and $O$ be finite types with decidable equality. Let $x : G \to$ `IntegerScalarCubeBox α S.value` (each $x(g)$ is a function from $\mathrm{Option}\ \alpha$ to the integers in $[-\texttt{S.value}, \texttt{S.value})$), let $u$ be an element of `PrincipalAxisTuples (allocatedGridAxis U basis S.value) (allocatedPrincipalSides B U basis S)` (integer tuples on the principal indices whose axis satisfies the predicate `allocatedGridAxis U basis S.value`, all defined by OpenAI), and let $\mathrm{rows} : O \to \mathrm{Finset}\ \alpha$.
--
--   **Hypotheses.** Let $j \in \mathrm{Fin}\ m$, $i \in I\ j$, and let $s$ be an embedding of $O$ into `BoundedIntegerExponent G (j + 1)` (exponent vectors on $G$ of total degree at most $j + 1$). Suppose the square integer matrix obtained from `scalarKernelIntegerJet x (j + 1) rows` (an integer jet matrix defined by OpenAI, with rows indexed by $O$ and columns by `BoundedIntegerExponent G (j + 1)`) by selecting the columns $s(o)$, $o \in O$, has nonzero determinant (call this hypothesis $hA$). Suppose $\sigma_j \le 1$. Let $y$ be a real-valued function on `PrincipalAxisParameter (fun a => ¬ allocatedGridAxis U basis S.value a)` (the parameters of the non-grid axes).
--
--   **Conclusion.** Write $a = \langle j, \mathrm{inl}\ i\rangle$ for the axis given by $i$. The pushforward of the probability measure `unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) a)` (the measure on real vectors indexed by the coefficient slots of degree $j + 1$ with a fixed smooth product density, defined by OpenAI) under the map `allocatedNormalizedProfileJet B U basis S x u rows a y` (a map to $O \to \mathbb{R}$ defined by OpenAI) is equal to the measure with density `allocatedContinuousKernelDensity B U basis S j i x u rows s hA y` (a real function on $O \to \mathbb{R}$ defined by OpenAI) with respect to Lebesgue measure on $O \to \mathbb{R}$ (the density being made nonnegative via `ENNReal.ofReal`).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileJet_unit_law_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileJet_unit_law` (in `lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B176` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Probability/AllocatedDensityParameterBounds.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedContinuousProfileJet_unit_law)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B176

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
theorem allocatedContinuousProfileJet_unit_law_s2 (j : Fin m) (i : I j)
    (s : O ↪ BoundedIntegerExponent G (j.val + 1))
    (hA : ((scalarKernelIntegerJet x (j.val + 1) rows).submatrix id s).det ≠ 0)
    (hσ1 : σ j ≤ 1)
    (y : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n) (α := α) (fun a => ¬grid a) → ℝ) :
    (unitCoefficientSource (SamplerCoefficientSlot G B (layerSamplerDegree I n) ⟨j, .inl i⟩)).map
        (allocatedNormalizedProfileJet B U basis S x u rows ⟨j, .inl i⟩ y) =
      realDensityMeasure volume (allocatedContinuousKernelDensity B U basis S j i x u rows s hA y) := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
