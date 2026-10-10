-- Prove2me | Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_mixed_grid_site_expansion
-- name    : OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-10T05:50:19.10233+00:00
-- url     : https://prove2.me/theorems/8e066945-d696-4c35-a666-0c05278040c9
-- title:
--   A site expansion approximates the supported sliced grid PMF on any grid axis to 2ε
-- statement:
--   Fix the section data: a natural number $m$; a finite type $G$; finite types $I_j$ with decidable equality and natural numbers $n_j$ ($j \in \mathrm{Fin}\,m$); finite types $B_a$ with decidable equality over the axes $a$ of `LayerSamplerAxis I n` (the sigma type $\Sigma_j\, I_j \oplus \mathrm{Fin}(n_j)$); finite types $J_j$, real subspaces $U_j \subseteq \mathbb R^{J_j}$ and bases `basis j` (indexed by $\mathrm{Fin}\,n_j$) of the orthogonal complements of `euclideanSubspace (U j)`; real functions $R, \sigma$ on $\mathrm{Fin}\,m$ with $R_j > 0$ (hR) and $\sigma_j > 0$ (hσ); a `LayerSamplerScale` $S$ (a structure bundling a positive natural number $S.\mathrm{value}$ with width and gap inequalities); a finite type $\alpha$ with decidable equality; $q \in \mathbb N$ with $q > 0$ (hq) and $r : \mathrm{FullInput} \to \mathrm{Option}\,\alpha \to \mathbb Z/q$, where FullInput $=$ `PrincipalTupleIndex B (layerSamplerDegree I n)`; $H, \mathrm{step} : \mathrm{FullInput} \to \mathbb N$ and $c : \mathrm{FullInput} \to \mathbb Z$ with $H_t > 0$ (hH) and each progression `integerProgressionSupport (c t) (step t) (H t)` $= \{c_t + \mathrm{step}_t k : 0 \le k < H_t\}$ contained in $[0,$ `allocatedPrincipalSides B U basis S t`$)$ (hsubset); the residue cell $\{y : \texttt{principalResidueLabel q y} = r\}$ of positive mass under `principalTupleWeights B (layerSamplerDegree I n) H hH` (hcell); and a layer $j$ with an index $i \in \mathrm{Fin}(n_j)$. Write height $=$ `basisAxisScale (basis j) i` $= \lceil\|\mathrm{basis}_j(i)\|^{-1}\rceil$, degree $= j+1$, $\gamma =$ `principalProfileSize (R j) |layerIntegerPrincipalSlots B j i|`, cost $=$ `inactiveDenominator γ` $\cdot\, 2^{\mathrm{degree}}$, and torusA, torusI $=$ `blockTorusFactor |α| degree |B ⟨j, inr i⟩| (4γ)`, resp. with last argument $1$.
--
--   Assume the axis $\langle j, \mathrm{inr}\,i\rangle$ satisfies `allocatedGridAxis U basis S.value` (hgrid); let $\delta > 0$ with $\delta\cdot$`allocatedPrincipalSides B U basis S ⟨⟨j, inr i⟩, b, v⟩` $\le H_{\langle j,\mathrm{inr}\,i\rangle,b,v}$ for all $b, v$; let $T \in \mathbb N$ with $(|\alpha|+1)q/\delta \le T$; assume $\mathrm{step}_{\langle j,\mathrm{inr}\,i\rangle,b,v} > 0$ for all $b, v$; let $A \in \mathbb R_{\ge 0}$ with `Real.smoothTransition` $A$-Lipschitz; let $P \ge 1$ with `scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1` $\le P$, `scalarCubePrimitiveEnvelope α A 1 0 q` $\le P$ and $\mathrm{step}_{\langle j,\mathrm{inr}\,i\rangle,b,v}\, q \le P$ for all $b, v$; let rows be a finset of finsets of $\alpha$, each of cardinality at most degree, with `positiveModerateSpectrumBlockCount j |rows| ((layerTailDegree m + 1)|rows|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$ and `uniformSpectrumBlockCount j |rows| (degree·|rows|)` $\le |B_{\langle j,\mathrm{inr}\,i\rangle}|$; and let $0 < \varepsilon \le 1$ with $\sigma_j \le 1$. Put $d = |\mathrm{rows}|$, $t_a = ($`layerTailDegree m`$+1)d$, $t_i = \mathrm{degree}\cdot d$, $V_a = (\mathrm{torusA}/(2\gamma))/\delta^{\mathrm{degree}}$, $V_i = \mathrm{torusI}\cdot\mathrm{cost}/\delta^{\mathrm{degree}}$, $W_a = \mathrm{torusA}^d/\delta^{t_a}$, $W_i = (\mathrm{torusI}\cdot\mathrm{cost})^d/\delta^{t_i}$, $\zeta_a =$ `positiveModerateRetainedBias j d ta P Va Wa ε`, $\zeta_i =$ `uniformBlockRetainedBias j d ti P Vi Wi ε`, $f_a =$ `positiveRetainedFrequencyBound j d P Va ζa` and $f_i =$ `uniformScaledRetainedFrequencyBound j d P Vi ζi` (both made nonnegative), $c_a =$ `positiveModerateSpectrumCardBudget j d ta P Va Wa 1` $+1$, $c_i =$ `uniformSpectrumAbsoluteCap j d ti P Vi Wi`, $K_{\max} =$ `allocatedSlicedGridHeightCutoff B j i T` (a natural number), and $R_0 = d\cdot|\texttt{BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree}|\cdot 2^{|\alpha|}(|\alpha|+1)^{\mathrm{degree}} R_j$.
--
--   Then for every real $Q \ge 0$ with $R_0 + 1/4 \le e^Q$, $(\varepsilon/(c_a+1))^{-1} \le e^Q$, $(\varepsilon/(c_i+1))^{-1} \le e^Q$, $(\texttt{CircleFourier.characterLipConstant}\cdot d f_a + 4)2^{|\alpha|} \le e^Q$, the same with $f_i$, $K_{\max}^d \le e^Q$, $d\cdot 2K_{\max}^2\cdot K_{\max}^d\cdot 2^{|\alpha|} \le e^Q$ and $\varepsilon^{-1} \le e^Q$, there exists a `ScalarSiteExpansion` $e$ on $\mathrm{Finset}\,\alpha$ (a finite family of terms $k$, each with a period $p_k$, a coefficient $a_k \in \mathbb C$ and factors $\phi_{k,s} : \mathbb Z/p_k \times \mathbb R \to \mathbb C$; its integer evaluation at height $N$ is $y \mapsto \sum_k a_k \prod_s \phi_{k,s}(y_s \bmod p_k, y_s/N)$) such that:
--
--   - `e.Bounds` holds with: at most $\max\bigl(1, \max(\texttt{positiveModerateSpectrumCardBudget j d ta P Va Wa ε},\ \texttt{uniformSpectrumSizeConstant j d ti P Vi Wi}/\varepsilon^{\max(\texttt{majorArcSpectrumExponent j d},\ \texttt{majorArcLengthExponent j}\cdot t_i)})\bigr)\cdot\exp(2^{|\alpha|}(4Q+8))$ terms; periods positive and at most $\max(1, \max(\texttt{positiveRetainedDenominatorBound j d ta P Va Wa ζa}, \texttt{uniformScaledRetainedDenominatorBound j d ti P Vi Wi ζi}))$; $\sum_k |a_k| \le \max(1, \max(c_a, c_i))\cdot\exp(2^{|\alpha|}(4Q+8)+Q)$; every factor of norm at most $1$ and $(\exp(1+6Q+12)+4)$-Lipschitz in its real argument; and every factor vanishing at real arguments $x$ with $|x| \ge R_0 + 1/4$; and
--   - for every $x : G \to$ `IntegerScalarCubeBox α S.value` and every $y : \mathrm{Finset}\,\alpha \to \mathbb Z$ whose Möbius coefficients `booleanCoefficient y t` vanish for all $t \notin \mathrm{rows}$,
--   $$\Bigl\| \mathrm{height}^{d}\cdot \texttt{allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x}\,(t \mapsto \texttt{booleanCoefficient y t}) - \texttt{e.integerEval height y} \Bigr\| \le 2\varepsilon.$$
--
--   Lean: `OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_mixed_grid_site_expansion` in `lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B055`, `OAIErdos3B145` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Sampling/AllocatedSupportedSlicedFullGridSite.lean#L44

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B055
import Definitions.Def_OAIErdos3B145

namespace OAI

section

namespace Erdos3.VectorPolynomial

universe uα

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
variable {α : Type uα} [Fintype α] [DecidableEq α]
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
local notation "denom" => inactiveDenominator gamma
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) (4 * gamma)
local notation "torusI" => blockTorusFactor (Fintype.card α) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

include hq in
theorem exists_allocatedSupportedSliced_mixed_grid_site_expansion
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
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hσ1 : σ j ≤ 1) :
    let d := rows.card
    let ta := (layerTailDegree m + 1) * d
    let ti := degree * d
    let Va := ((torusA : ℝ) / (2 * gamma)) / δ ^ degree
    let Vi := (torusI : ℝ) * cost / δ ^ degree
    let Wa := (torusA : ℝ) ^ d / δ ^ ta
    let Wi := ((torusI : ℝ) * cost) ^ d / δ ^ ti
    let ζa := positiveModerateRetainedBias j.val d ta P Va Wa ε
    let ζi := uniformBlockRetainedBias j.val d ti P Vi Wi ε
    let fa := Real.toNNReal (positiveRetainedFrequencyBound j.val d P Va ζa)
    let fi := Real.toNNReal (uniformScaledRetainedFrequencyBound j.val d P Vi ζi)
    let ca := positiveModerateSpectrumCardBudget j.val d ta P Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap j.val d ti P Vi Wi
    let Kmax := allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T
    let R0 := (d : ℝ) *
      ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
        ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ degree) * R j)
    ∀ {Q : ℝ}, 0 ≤ Q → R0 + 1 / 4 ≤ Real.exp Q →
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q → (ε / (ci + 1))⁻¹ ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fa) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ((CircleFourier.characterLipConstant * (d * fi) + 4) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      (Kmax : ℝ) ^ d ≤ Real.exp Q →
      ((d * (2 * (Kmax : ℝ≥0) ^ 2) * (Kmax : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ Fintype.card α : ℝ≥0) ≤ Real.exp Q →
      ε⁻¹ ≤ Real.exp Q →
    ∃ e : ScalarSiteExpansion.{uα,uα} (Finset α),
      e.Bounds
        (max 1 (max (positiveModerateSpectrumCardBudget j.val d ta P Va Wa ε)
          (uniformSpectrumSizeConstant j.val d ti P Vi Wi /
            ε ^ max (majorArcSpectrumExponent j.val d) (majorArcLengthExponent j.val * ti))) *
          Real.exp (Fintype.card (Finset α) * (4 * Q + 8)))
        (max 1 (max (positiveRetainedDenominatorBound j.val d ta P Va Wa ζa)
          (uniformScaledRetainedDenominatorBound j.val d ti P Vi Wi ζi)))
        (max 1 (max ca ci) * Real.exp (Fintype.card (Finset α) * (4 * Q + 8) + Q))
        (⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ + 4) (R0 + 1 / 4) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (y : Finset α → ℤ),
        (∀ t ∉ rows, booleanCoefficient y t = 0) →
        ‖(((height : ℝ) ^ rows.card *
          (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x
            (fun t => booleanCoefficient y t)).toReal : ℝ) : ℂ) - e.integerEval height y‖ ≤ 2 * ε := by
  sorry

end Erdos3.VectorPolynomial
end
end OAI
