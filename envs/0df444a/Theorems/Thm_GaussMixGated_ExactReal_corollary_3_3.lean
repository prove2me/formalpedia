-- Prove2me | Theorems.Thm_GaussMixGated_ExactReal_corollary_3_3
-- name    : GaussMixGated.ExactReal.corollary_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T15:25:30.102768+00:00
-- url     : https://prove2.me/theorems/fe179ba6-9117-45c8-a0c2-ccf019bd7730
-- title:
--   Corollary 3.3 — The actual accepted moment
-- statement:
--   Let latent atoms $u_1,\dots,u_s\in\mathbb R^n$ have weights $w_i>0$, $\sum_iw_i=1$. Given the atom, the gate side $A$ and the query side $B$ are independent $N(u_i,vI_n)$, $v>0$. Let $H_0(A,R_0)$ be an arbitrary measurable prior history with randomness $R_0$ independent of everything else, and let $H_1$ be the event that $H_0$ accepts and the gate of Lemma 3.2 (degree $q$, threshold $T>0$, fresh sketches) accepts $A$. With $a_1(u)=\mathbb P(H_1\mid u)$,
--
--   $$\mathbb E\big[1_{H_1}\|F(B)\|^2\big]=\sum_iw_i\,a_1(u_i)\,M(u_i)\le\sqrt{K_q}\,T.$$
--
--   The moment measured on the independent query side is the true moment of the accepted latent measure, including remote atoms that pass the gate.
--
--   Differences from the source:
--   - encoding: §3.1 views A₀ = X + Z, B₀ = X − Z, conditionally independent given the atom → an explicit product space (atom index, G_A, G_B, R₀, sketches) with A = u_I + √v G_A, B = u_I + √v G_B; reason: this is the conditional-independence structure §3.1 derives; it builds it in rather than assuming it
--   - encoding: E[1_{H₁}‖F(B)‖²] → lower Lebesgue integral in ℝ≥0∞; reason: nonnegative integrand; no integrability side condition
-- source:
--   Zheng, Xie, He, Learning Finite Gaussian Location Mixtures via Gated Moments and Posterior Covers, STOC 2027 submission #36 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/36.pdf, PDF p. 11 (printed p. 9), Corollary 3.3, (19); setting §3.1, PDF pp. 8–9

import Mathlib
import Definitions.Def_GaussMixGated_ExactReal_Jet

open MeasureTheory

namespace GaussMixGated.ExactReal

/-- Corollary 3.3 (The actual accepted moment) (Zheng–Xie–He, STOC 2027 #36, PDF p. 11): appending
the gate of Lemma 3.2 to an arbitrary prior history `H₀(A, R₀)` evaluated on the gate side,
`E[1_{H₁} ‖F(B)‖²] = ∑_i w_i a₁(u_i) M(u_i) ≤ √K_q · T` on the independent query side. -/
theorem corollary_3_3 {s n r : ℕ} (F : PolyMap n r) (q : ℕ) (hF : F.DegLE q) (v T : ℝ)
    (hv : 0 < v) (hT : 0 < T) (w : Fin s → ℝ) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (u : Fin s → Fin n → ℝ) {Ω₀ : Type*} [MeasurableSpace Ω₀] (lam₀ : Measure Ω₀)
    [IsProbabilityMeasure lam₀] (H₀ : (Fin n → ℝ) → Ω₀ → Prop)
    (hH₀ : MeasurableSet {p : (Fin n → ℝ) × Ω₀ | H₀ p.1 p.2}) :
    ∫⁻ ω, {ω : Fin s × (Fin n → ℝ) × (Fin n → ℝ) × Ω₀ × (Fin 8 → SketchNoise n q) |
          H₀ (u ω.1 + Real.sqrt v • ω.2.1) ω.2.2.2.1 ∧
            GateAccepts F q v T ω.2.2.2.2 (u ω.1 + Real.sqrt v • ω.2.1)}.indicator
        (fun ω => ENNReal.ofReal (sqNorm (F.eval (u ω.1 + Real.sqrt v • ω.2.2.1)))) ω
        ∂viewHistoryLaw (n := n) (q := q) w lam₀ =
      ENNReal.ofReal
        (∑ i, w i * appendedAcceptance F q v T lam₀ H₀ (u i) * momentM F v (u i)) ∧
    ∑ i, w i * appendedAcceptance F q v T lam₀ H₀ (u i) * momentM F v (u i) ≤
      Real.sqrt (Kconst q) * T := by sorry

end GaussMixGated.ExactReal
