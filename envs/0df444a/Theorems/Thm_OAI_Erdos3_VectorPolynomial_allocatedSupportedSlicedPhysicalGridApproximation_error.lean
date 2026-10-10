-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridApproximation_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridApproximation_error
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T16:26:29.409786+00:00
-- url     : https://prove2.me/theorems/2dfc85fc-ad27-42ff-8c35-8f5ccde7cf6a
-- title:
--   Spectral approximation of the physical grid PMF on an active grid axis
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q>0$ (`hq`); write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`. Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ (`hsubset`), and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Fix $j\in\mathrm{Fin}\,m$, $i\in\mathrm{Fin}\,n_j$, write $a_0=\langle j,\mathrm{inr}\,i\rangle$, and assume $\texttt{S.value}^{j+1}<\mathrm{height}:=$ `basisAxisScale (basis j) i` (`hactive`) and $(|\alpha|+1)q\le H_{\langle a_0,b,v\rangle}$ for all $b,v$ (`hsize`). Let $\gamma=$ `principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|` $=R_j/(8(|\cdot|+1))$ and $\mathrm{torus}=$ `blockTorusFactor |α| (j + 1) |B(a₀)| (4 * γ)` (a natural number). Assume `allocatedGridAxis U basis S.value a₀` (`hgrid`, i.e. $\mathrm{height}\le\texttt{S.value}^{\texttt{layerTailDegree}\ m+1}$ with `layerTailDegree m` $=m(2^{m+1}+1)$); $\delta>0$ with $\delta\cdot\texttt{S.value}\le H_{\langle a_0,b,v\rangle}$ and $0<\mathrm{step}_{\langle a_0,b,v\rangle}$ for all $b,v$; $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz; a real $P$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle a_0,b,v\rangle}\,q\le P$ for all $b,v$ (`probabilityProfileLipschitz` is a nonnegative real constant); a real $\varepsilon$ and a natural number $M\ne0$ with $M=\mathrm{torus}\cdot\mathrm{height}$; `rows` a `Finset (Finset α)` whose members have at most $j+1$ elements, with `positiveModerateSpectrumBlockCount j |rows| ((layerTailDegree m + 1) * |rows|)` $\le|B(a_0)|$; and $0<\varepsilon\le1$. Let $V=(\mathrm{torus}/(2\gamma))/\delta^{j+1}$, $t=($`layerTailDegree m`$+1)\,|\mathrm{rows}|$, $W=\mathrm{torus}^{|\mathrm{rows}|}/\delta^{t}$, and $F=$ `positiveModerateSpectrumCover rows M j P V (δ * S.value) (positiveModerateRetainedBias j |rows| t P V W ε)` (a finite set of frequencies $k\colon\mathrm{rows}\to\mathrm{Fin}\,M$). Then $|F|\le$ `positiveModerateSpectrumCardBudget j |rows| t P V W ε` (an explicit real number), and for every $x\colon G\to$ `IntegerScalarCubeBox α S.value` and every $z\colon\mathrm{rows}\to\mathbb Z$,
--   $$\big\|\mathrm{height}^{|\mathrm{rows}|}\,\pi_x(z)-\texttt{allocatedSupportedSlicedPhysicalGridApproximation}\ B\ U\ \mathrm{basis}\ \mathrm{hR}\ \mathrm{hσ}\ S\ q\ \mathrm{hq}\ r\ H\ \mathrm{step}\ c\ \mathrm{hH}\ j\ i\ \mathrm{hactive}\ \mathrm{hsize}\ M\ \mathrm{rows}\ F\ z\big\|\le\varepsilon,$$
--   where $\pi_x(z)$ is the probability of $z$ under `allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x` (draw $y$ from `containedSupportedProgressionLaw B (layerSamplerDegree I n) (allocatedPrincipalSides B U basis S) H step c … hH hsubset q r hcell`, then take the image of `allocatedLayerIntegerPMFs B U basis hR hσ S j i` under `integerMatrixImagePMF` of the `boundedCoefficientJetMatrix` of `allocatedPhysicalCubeRoot … x y` and `allocatedPhysicalCubeDirections … x y` in degree $j+1$), and `allocatedSupportedSlicedPhysicalGridApproximation … z` is the complex number obtained by integrating `weightedAffineModeratePlateauApproximation` (a `normalizedSupportPlateau` cutoff times a grid approximation over $F$, built from `allocatedPrincipalNormalizedSource`, the supported axis sources, the lower ends $c_{\langle a_0,b,v\rangle}$, the strides, height and the radius `blockJetScaleBound |α| (j + 1) |B(a₀)| (4 * γ)`) against the law `allocatedLayerIntegerPMFs B U basis hR hσ S j i` at the constant coefficient slot, with the constant `booleanCoefficient` shift.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedPhysicalGridApproximation_error` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedInactiveGridSite.lean#L73

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

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

local notation "coeff" => (fun _ : B (Sigma.mk j (Sum.inr i)) =>
  allocatedPrincipalNormalizedSource B U basis hR S j i hactive)
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin (Fin.val j + 1)) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

local notation "radius" => blockJetScaleBound (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "height" => basisAxisScale (basis j) i
local notation "torus" => blockTorusFactor (Fintype.card α) (Fin.val j + 1)
  (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell
local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

theorem allocatedSupportedSlicedPhysicalGridApproximation_error
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j, Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * S.value ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ j.val + 1)
    (hB : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := ((torus : ℝ) / (2 * gamma)) / δ ^ (j.val + 1)
    let t := (layerTailDegree m + 1) * rows.card
    let W := (torus : ℝ) ^ rows.card / δ ^ t
    let F := positiveModerateSpectrumCover rows M j.val P V (δ * S.value)
      (positiveModerateRetainedBias j.val rows.card t P V W ε);
    (F.card : ℝ) ≤ positiveModerateSpectrumCardBudget j.val rows.card t P V W ε ∧
    ∀ (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ),
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ) -
        allocatedSupportedSlicedPhysicalGridApproximation B U basis hR hσ S q hq r H step c hH j i
          hactive hsize M rows F z‖ ≤ ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
