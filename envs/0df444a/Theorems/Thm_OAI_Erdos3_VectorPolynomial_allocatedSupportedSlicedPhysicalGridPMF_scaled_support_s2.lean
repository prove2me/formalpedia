-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:27:36.894269+00:00
-- url     : https://prove2.me/theorems/adaa4c2d-e371-4580-a23f-4bda7b134877
-- title:
--   Values in the support of the supported sliced physical grid law, divided by the axis height, are bounded
-- statement:
--   Let $m$ be a natural number and $G$ a finite type. For $j \in \operatorname{Fin} m$ let $I_j$ (with decidable equality) and $J_j$ be finite types and $n_j$ a natural number; let $B$ assign a finite type with decidable equality to each element of `LayerSamplerAxis I n` (pairs $(j, a)$ with $a \in I_j \sqcup \operatorname{Fin} n_j$). For each $j$ let $U_j$ be a real subspace of $J_j \to \mathbb{R}$ and `basis j` a real basis, indexed by $\operatorname{Fin} n_j$, of the orthogonal complement of `euclideanSubspace (U j)` (that subspace in the Euclidean space $\mathbb{R}^{J_j}$; defined by OpenAI). Let $R, \sigma : \operatorname{Fin} m \to \mathbb{R}$ with $R_j > 0$ and $\sigma_j > 0$ for all $j$, and let $S$ be a `LayerSamplerScale B U basis R σ` (OpenAI's structure containing a positive natural number `S.value`). Let $\alpha$ be a finite type with decidable equality.
--
--   Let $q$ be a natural number and $r$ a residue assignment from `PrincipalTupleIndex B (layerSamplerDegree I n)` to $\mathrm{Option}\ \alpha \to \mathbb{Z}/q$. Let $H, \mathrm{step}$ (natural numbers) and $c$ (integers) be functions on `PrincipalTupleIndex B (layerSamplerDegree I n)` with $H(t) > 0$ and (hsubset) the progression `integerProgressionSupport (c t) (step t) (H t)` (the integers $c(t) + \mathrm{step}(t)\, k$, $0 \le k < H(t)$) contained in $[0, \texttt{allocatedPrincipalSides B U basis S t})$ for every $t$, and such that (hcell) the cell of principal integer tuples whose residues modulo $q$ equal $r$ has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (the product of uniform cube laws with sizes $H$). Let $j \in \operatorname{Fin} m$ and $i \in \operatorname{Fin} n_j$ with $\sigma_j \le 1$, let `rows` be a finite set of subsets of $\alpha$, and let $x : G \to$ `IntegerScalarCubeBox α S.value` (functions $\mathrm{Option}\ \alpha \to [-\texttt{S.value}, \texttt{S.value}) \cap \mathbb{Z}$).
--
--   Let $z : \texttt{rows} \to \mathbb{Z}$ have nonzero mass under `allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x`, OpenAI's probability mass function on $\texttt{rows} \to \mathbb{Z}$ obtained by drawing a principal tuple $y$ from `containedSupportedProgressionLaw` (with sides `allocatedPrincipalSides B U basis S`, lengths $H$, steps, starts $c$, modulus $q$ and residues $r$) and then taking the image of the layer integer law `allocatedLayerIntegerPMFs B U basis hR hσ S j i` under the bounded coefficient jet matrix of the physical cube determined by $x$ and $y$ (in degree $j+1$, with rows indexed by `rows`). Then for every $t \in \texttt{rows}$,
--   $$\Bigl| \frac{z(t)}{h} \Bigr| \le K \cdot 2^{|\alpha|} (|\alpha| + 1)^{j+1} \cdot R_j,$$
--   where $h$ = `basisAxisScale (basis j) i` $= \lceil \lVert \texttt{basis}_j(i) \rVert^{-1} \rceil$ and $K$ is the number of elements of `BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j+1)` (exponent vectors of total degree at most $j+1$ on OpenAI's sampler variables).
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_scaled_support` (in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B196` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_scaled_support)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196

section

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i

theorem allocatedSupportedSlicedPhysicalGridPMF_scaled_support_s2
    (hσ1 : σ j ≤ 1) (rows : Finset (Finset α)) (x : G → IntegerScalarCubeBox α S.value)
    (z : rows → ℤ)
    (hmass : allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z ≠ 0)
    (t : rows) : |(z t : ℝ) / height| ≤
      (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) * R j := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
