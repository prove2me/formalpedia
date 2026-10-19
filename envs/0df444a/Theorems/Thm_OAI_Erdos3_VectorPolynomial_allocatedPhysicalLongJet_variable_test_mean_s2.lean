-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedPhysicalLongJet_variable_test_mean_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:16:34.947525+00:00
-- url     : https://prove2.me/theorems/a6649c66-3a2f-47ec-838d-39fa2f9e570f
-- title:
--   Averaging a bounded test of the physical long jet against the coefficient source, with the test depending on a mixed tuple
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$ (with decidable equality), $J_j$, $O_j$ (with decidable equality) be finite types and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and $b_j$ a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$, $\sigma_j > 0$ and $\sigma_j \le 1$ for all $j$, and let $S$ be a `LayerSamplerScale B U b R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality and $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\ \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$). Write `grid` for OpenAI's predicate `allocatedGridAxis U b S.value` on axes and `sides` for `allocatedPrincipalSides B U b S`; let $u$ be a principal integer tuple on the grid axes. Let `rows j` $: O_j \to$ finite subsets of $\alpha$, and for each $j$ let $s_j : O_j \hookrightarrow$ `BoundedIntegerExponent G (j+1)` be an embedding such that (hA) the square submatrix of `scalarKernelIntegerJet x (j+1) (rows j)` (OpenAI's integer jet matrix) on the columns $s_j$ has nonzero determinant.
--
--   Let `source` = `allocatedCoefficientSource B U b hR hσ S`, OpenAI's product probability measure on the coefficient sample arrays `CoefficientSamplerArrays I n` (for the variables `LayerSamplerVariables G I n B`); let `split` = `allocatedCoefficientSplit B U b S`, OpenAI's measurable bijection of these arrays with pairs (frozen coefficients on grid axes, `AllocatedFrozenCoefficients B U b S`; long coefficients on non-grid axes); let `frozenSource` = `allocatedFrozenCoefficientSource B U b hR hσ S` (the corresponding product measure on frozen coefficients); and let `reference` = `allocatedLongJetReference B U b S O` (OpenAI's product reference measure on `AllocatedLongJetRows B U b S O`, the long jet rows on non-grid axes).
--
--   Let $w$ be a finite probability weight on the principal integer tuples on the non-grid axes, and let $\varphi(v, a, z) \in \mathbb{C}$, for such tuples $v$, frozen coefficients $a$ and long jet rows $z$, be such that for each $v$ the map $(a, z) \mapsto \varphi(v, a, z)$ is measurable, and $\lVert \varphi(v, a, z) \rVert \le C$ for all $v, a, z$ (for some real $C$). Write $\mathbb{E}_w$ for the weighted mean $\sum_v w(v)\,(\cdot)$. Then
--   $$\int \mathbb{E}_{v \sim w}\, \varphi\bigl(v, (\texttt{split } a)_1, \texttt{allocatedPhysicalLongJetMap B U b S x u v rows } a\bigr) \, d\,\texttt{source}(a) = \int \int \mathbb{E}_{v \sim w} \bigl[ \rho_v(z)\, \varphi(v, a_0, z) \bigr] \, d\,\texttt{reference}(z) \, d\,\texttt{frozenSource}(a_0),$$
--   where `allocatedPhysicalLongJetMap B U b S x u v rows a` is OpenAI's map sending coefficient arrays to the long jet rows of the physical cube determined by $x$, $u$, $v$, and $\rho_v$ = `allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1`, OpenAI's real density on long jet rows (a product of per-axis factors).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean` (in `lean/OAI/Combinatorics/Progressions/Estimates/AllocatedPhysicalLongImage.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B194` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Estimates/AllocatedPhysicalLongImage.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedPhysicalLongJet_variable_test_mean)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B194

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory

variable {m : ℕ} {G : Type*} [Fintype G] {I : Fin m → Type*} [∀ j, Fintype (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)

local notation "grid" => allocatedGridAxis (I := I) U b (LayerSamplerScale.value S)
local notation "sides" => allocatedPrincipalSides B U b S
local notation "split" => allocatedCoefficientSplit B U b S
local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "frozenSource" => allocatedFrozenCoefficientSource B U b hR hσ S
local notation "longSource" => allocatedLongCoefficientSource B U b hR hσ S

variable (u : PrincipalAxisTuples (α := α) (allocatedGridAxis (I := I) U b S.value)
  (allocatedPrincipalSides B U b S))
variable (v : PrincipalAxisTuples (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a)
  (allocatedPrincipalSides B U b S))
variable {O : Fin m → Type*} [∀ j, Fintype (O j)] [∀ j, DecidableEq (O j)]
variable (rows : ∀ j, O j → Finset α)

variable (s : ∀ j, O j ↪ BoundedIntegerExponent G (j.val + 1))
variable (hA : ∀ j, ((scalarKernelIntegerJet x (j.val + 1) (rows j)).submatrix id (s j)).det ≠ 0)
variable (hσ1 : ∀ j, σ j ≤ 1)

variable [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)]

theorem allocatedPhysicalLongJet_variable_test_mean_s2
    (w : FiniteProbabilityWeights (PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides))
    (φ : PrincipalAxisTuples (α := α) (fun a => ¬grid a) sides →
      AllocatedFrozenCoefficients B U b S → AllocatedLongJetRows B U b S O → ℂ)
    (hφ : ∀ v, Measurable (fun p : AllocatedFrozenCoefficients B U b S × AllocatedLongJetRows B U b S O =>
      φ v p.1 p.2)) {C : ℝ} (hbound : ∀ v a z, ‖φ v a z‖ ≤ C) :
    (∫ a, w.complexMean (fun v => φ v (split a).1
      (allocatedPhysicalLongJetMap B U b S x u v rows a)) ∂source) =
      ∫ a₀, ∫ z, w.complexMean (fun v =>
        (allocatedLongJetDensity B U b hR hσ S x u v rows s hA hσ1 z : ℂ) * φ v a₀ z)
        ∂allocatedLongJetReference B U b S O ∂frozenSource := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
