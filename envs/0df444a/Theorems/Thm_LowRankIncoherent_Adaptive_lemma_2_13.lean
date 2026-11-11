-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_lemma_2_13
-- name    : LowRankIncoherent.Adaptive.lemma_2_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:12.593978+00:00
-- url     : https://prove2.me/theorems/4c809e44-eb16-47e2-94fc-1fee23cc859b
-- title:
--   Lemma 2.13 — regularized channel decomposition
-- statement:
--   In the standing dimensions let $E$ have Kraus rank exactly $r$, let $σ$ be a positive definite input state, and let $s>0$. Set $X=E(|\sqrt σ⟩⟩⟨⟨\sqrt σ|)$ and $E_s=Φ_σ(X_s)$. Both $E_s$ and $E-E_s$ are completely positive and trace-nonincreasing. Moreover,
--   $$E-E_s=sΦ_σ(f_s(X)),\qquad\|E-E_s\|_⋄=s\|H_s(σ)\|_∞,\qquad E_s^†(I_b)=I_a-sH_s(σ).$$
--   The statement includes the exact decomposition, exact bias identity, output trace identity, and both positivity and trace conditions. It identifies the regularization bias without treating the regularized map as trace preserving.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Lemma 2.13, printed p. 16 = PDF p. 16; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem lemma_2_13 {a b r : ℕ} (ha : 0 < a) (hb : 2 ≤ b) (hrpos : 1 ≤ r)
    (hrmax : r ≤ a*b) (hfeasible : a ≤ r*b) (E : Map a b)
    (hE : E ∈ ChanTomoNB.QChan r a b) (hrank : (choi E).rank = r)
    (σ : Input a) (hσ : State σ) (hpd : σ.PosDef) (s : ℝ) (hs : 0 < s) :
    let X := outputState E σ
    let Es := reconstruct σ (regularized s X)
    CP Es ∧ TNI Es ∧ CP (E-Es) ∧ TNI (E-Es) ∧
    E-Es = (s : ℂ) • reconstruct σ (fs s X) ∧
    ChanTomoNB.diamondDist E Es = s * opNorm (sensitivity E s σ) ∧
    adjointI σ (regularized s X) = 1 - (s : ℂ) • sensitivity E s σ := by sorry

end LowRankIncoherent.Adaptive
