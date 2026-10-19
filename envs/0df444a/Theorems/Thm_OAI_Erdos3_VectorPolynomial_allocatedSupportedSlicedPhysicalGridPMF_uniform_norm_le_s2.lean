-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T04:43:22.427009+00:00
-- url     : https://prove2.me/theorems/da28677b-dc13-47b4-93c3-bc2af0438744
-- title:
--   Uniform point bound for the physical grid PMF on a grid axis
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q>0$ (`hq`); write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`. Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ (`hsubset`), and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Fix $j\in\mathrm{Fin}\,m$, $i\in\mathrm{Fin}\,n_j$ and write $a_0=\langle j,\mathrm{inr}\,i\rangle$, $\mathrm{height}=$ `basisAxisScale (basis j) i`, $\mathrm{degree}=j+1$. Assume `allocatedGridAxis U basis S.value a₀` (`hgrid`); $\delta>0$ with $\delta\cdot$ `allocatedPrincipalSides B U basis S ⟨a₀, b, v⟩` $\le H_{\langle a_0,b,v\rangle}$ for all $b,v$ (`hdense`); a natural number $T$ with $(|\alpha|+1)q/\delta\le T$; $0<\mathrm{step}_{\langle a_0,b,v\rangle}$ for all $b,v$; $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz; a real $P\ge1$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle a_0,b,v\rangle}\,q\le P$ for all $b,v$ (`probabilityProfileLipschitz` is a nonnegative real constant); and `rows` a `Finset (Finset α)` whose members have at most $\mathrm{degree}$ elements, with `positiveModerateSpectrumBlockCount j |rows| ((layerTailDegree m + 1) * |rows|)` $\le|B(a_0)|$ and `uniformSpectrumBlockCount j |rows| (degree * |rows|)` $\le|B(a_0)|$. Then for every $x\colon G\to$ `IntegerScalarCubeBox α S.value` and every $z\colon\mathrm{rows}\to\mathbb Z$,
--   $$\mathrm{height}^{|\mathrm{rows}|}\cdot\pi_x(z)\le\texttt{allocatedSlicedGridPointCap}\ B\ j\ i\ \delta\ P\ T\ |\mathrm{rows}|,$$
--   where $\pi_x(z)$ is the probability of $z$ under `allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x` (draw $y$ from `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step c … hH hsubset q r hcell`, then take the image of `allocatedLayerIntegerPMFs B U basis hR hσ S j i` under `integerMatrixImagePMF` of the `boundedCoefficientJetMatrix` of `allocatedPhysicalCubeRoot … x y` and `allocatedPhysicalCubeDirections … x y` in degree $j+1$), and `allocatedSlicedGridPointCap B j i δ P T d` is the real number $\max\big(1,\ (\texttt{allocatedSlicedGridHeightCutoff}\ B\ j\ i\ T)^{d},\ \texttt{positiveModerateSpectrumCardBudget}(\ldots)+1,\ \texttt{uniformSpectrumAbsoluteCap}(\ldots)\big)$ with arguments built from $j$, $d$, $P$, $\delta$, `layerTailDegree m`, `blockTorusFactor`, `principalProfileSize (R j) …` and `inactiveDenominator`.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2`, which states OpenAI's `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le` (in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedNaturalCap.lean`); the definitions it uses are in the definitions bundle `OAIE3v2B217` of version 2 of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedNaturalCap.lean (declaration OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le)

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217

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

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((height : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T rows.card := by
  sorry

end Erdos3.VectorPolynomial

end

end OAI
end
