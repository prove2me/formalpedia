-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedInactivePointApproximation_error
-- name    : OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactivePointApproximation_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-09T16:24:14.598733+00:00
-- url     : https://prove2.me/theorems/1003fd14-2f11-4a7d-8fe4-424330895a40
-- title:
--   Pointwise spectral approximation of the residue-jet PMF on a small inactive axis
-- statement:
--   Let $m\in\mathbb N$, $G$ a finite type, $I\colon\mathrm{Fin}\,m\to$ Type a family of finite types with decidable equality, $n\colon\mathrm{Fin}\,m\to\mathbb N$, $B$ a family of finite types with decidable equality indexed by `LayerSamplerAxis I n` $=\Sigma_j\,I_j\oplus\mathrm{Fin}\,n_j$, $J\colon\mathrm{Fin}\,m\to$ Type finite types, $U_j$ a subspace of $\mathbb R^{J_j}$, `basis` $j$ a basis indexed by $\mathrm{Fin}\,n_j$ of the orthogonal complement of `euclideanSubspace (U j)`, $R,\sigma\colon\mathrm{Fin}\,m\to\mathbb R$ with $R_j>0$ and $\sigma_j>0$ (`hR`, `hσ`), and $S$ a `LayerSamplerScale B U basis R σ` (a structure bundling a positive natural number `S.value` with width and gap conditions). Let $\alpha$ be a finite type with decidable equality and $q>0$ (`hq`); write $\mathcal T=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`. Let $r\colon\mathcal T\to\mathrm{Option}\,\alpha\to\mathbb Z/q$, $H,\mathrm{step}\colon\mathcal T\to\mathbb N$ with $H_t>0$ (`hH`) and $c\colon\mathcal T\to\mathbb Z$, with `integerProgressionSupport (c t) (step t) (H t)` $=\{c_t+\mathrm{step}_t\,i:0\le i<H_t\}\subseteq[0,\ $`allocatedPrincipalSides B U basis S t`$)$ (`hsubset`), and assume (`hcell`) that the event `principalResidueLabel q y = r` has positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH`. Fix $j\in\mathrm{Fin}\,m$, $i\in\mathrm{Fin}\,n_j$, write $a_0=\langle j,\mathrm{inr}\,i\rangle$, and assume $(|\alpha|+1)q\le H_{\langle a_0,b,v\rangle}$ for all $b,v$ (`hsize`). Put $\mathrm{height}=$ `basisAxisScale (basis j) i`, $\mathrm{degree}=j+1$, $\mathrm{denom}=$ `inactiveDenominator (principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|)` $=\max(1,\lceil\gamma^{-1}\rceil)$ where $\gamma=R_j/(8(|\cdot|+1))$, $\mathrm{side}=$ `inactiveSideLength degree height denom` (the integer $\mathrm{degree}$-th root of $\lfloor\mathrm{height}/\mathrm{denom}\rfloor$ if $2\,\mathrm{denom}\le\mathrm{height}$, else $1$), $\mathrm{cost}=\mathrm{denom}\cdot2^{\mathrm{degree}}$, `sources` $=$ `principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r a₀ hsize` (a `NormalizedScalarCubeSource α` for each $b\in B(a_0)$ and $v<\mathrm{degree}$), $\mathrm{lower}(b,v,a)=c_{\langle a_0,b,v\rangle}$ if $a=\mathrm{none}$ and $0$ otherwise, $\mathrm{strides}(b,v,\_)=\mathrm{step}_{\langle a_0,b,v\rangle}$, $\mathrm{radius}=$ `blockJetScaleBound |α| degree |B(a₀)| 1` $=|B(a_0)|\,2^{\mathrm{degree}}(|\alpha|+1)^{\mathrm{degree}}$ and $\mathrm{torus}=$ `blockTorusFactor |α| degree |B(a₀)| 1` (a natural number). Assume $\mathrm{height}\le\texttt{S.value}^{\mathrm{degree}}$, $2\,\mathrm{denom}\le\mathrm{height}$; $\delta>0$ with $\delta\cdot\mathrm{side}\le H_{\langle a_0,b,v\rangle}$ and $0<\mathrm{step}_{\langle a_0,b,v\rangle}$ for all $b,v$; $A\ge0$ with `Real.smoothTransition` $A$-Lipschitz; $P\ge1$ with `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle a_0,b,v\rangle}\,q\le P$ for all $b,v$; a real $\varepsilon$ and a natural number $M\ne0$ with $M=\mathrm{torus}\cdot\mathrm{height}$; `rows` a `Finset (Finset α)` whose members have at most $\mathrm{degree}$ elements, with `uniformSpectrumBlockCount j |rows| (degree * |rows|)` $\le|B(a_0)|$; and $0<\varepsilon\le1$. Let $V=\mathrm{torus}\cdot\mathrm{cost}/\delta^{\mathrm{degree}}$, $t=\mathrm{degree}\cdot|\mathrm{rows}|$, $W=(\mathrm{torus}\cdot\mathrm{cost})^{|\mathrm{rows}|}/\delta^{t}$, $\zeta=$ `uniformBlockRetainedBias j |rows| t P V W ε` and $F=$ `uniformBlockSpectrumCover rows M j P V (δ * side) ζ` (a finite set of frequencies $k\colon\mathrm{rows}\to\mathrm{Fin}\,M$). Then: (1) $|F|\le$ `uniformSpectrumSizeConstant j |rows| t P V W` $/\ \varepsilon^{\max(e_1,\,e_2t)}$ with $e_1=$ `majorArcSpectrumExponent j |rows|` and $e_2=$ `majorArcLengthExponent j`; (2) $\sum_k\big\|\prod_b$ `affineWeightedCubeGridCoefficient (sources b) (lower b) (strides b) M rows k`$\big\|\le$ `uniformSpectrumAbsoluteCap j |rows| t P V W`, the sum over all $k\colon\mathrm{rows}\to\mathrm{Fin}\,M$; and (3) for all `shift`, $z\colon\mathrm{rows}\to\mathbb Z$,
--   $$\Big\|\mathrm{height}^{|\mathrm{rows}|}\,\pi(z)-\texttt{normalizedSupportPlateau}\ \mathrm{radius}\ \Big(\tfrac{z-\mathrm{shift}}{\mathrm{height}}\Big)\cdot\texttt{integerGridApproximation}\ (\texttt{weightedCubeIntegerSource sources})\ (\texttt{affineWeightedCubeIntegerSum sources lower strides rows shift})\ \mathrm{height}\ M\ F\ z\Big\|\le\varepsilon,$$
--   where $\pi(z)$ is the probability of $z$ under `allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift`; `normalizedSupportPlateau H x` is `linearCutoff H (1/4) ‖x‖` (a real cutoff in the norm of $x$); and `integerGridApproximation p Y K M F z` $=(K/M)^{|\mathrm{rows}|}\sum_{k\in F}$ `integerGridCoefficient p Y M k` $\cdot\overline{\texttt{rectangularGridCharacter}\ M\ k\ z}$.
--
--   Lean: `OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactivePointApproximation_error` in `lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveFixedCap.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Geometry/AllocatedSupportedSlicedInactiveFixedCap.lean#L81

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

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

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

local notation "radius" => blockJetScaleBound (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1
local notation "torus" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

theorem allocatedSupportedSlicedInactivePointApproximation_error
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {ε : ℝ} {M : ℕ} [NeZero M] (hM : M = torus * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := (torus : ℝ) * cost / δ ^ degree
    let t := degree * rows.card
    let W := ((torus : ℝ) * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ shift z : rows → ℤ,
      ‖(((height : ℝ) ^ rows.card *
        (allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift z).toReal : ℝ) : ℂ) -
        (normalizedSupportPlateau radius (fun t => ((z t : ℝ) - shift t) / height) : ℂ) *
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
