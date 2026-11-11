-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_proposition_3_15
-- name    : LowRankIncoherent.Adaptive.proposition_3_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:19.268502+00:00
-- url     : https://prove2.me/theorems/9eec1074-0a52-4890-a296-deb1a11364f9
-- title:
--   Proposition 3.15 — full TwoBatch error bounds
-- statement:
--   In the standing feasible dimensions let $E$ have Kraus rank at most $r$ and fix a state $σ\succeq I_a/(2a)$. Let $0<s≤\min\{1,\sqrt{a/r}\}$ and $0<δ<1$. There is an absolute $K>0$ for which $b_0=D+(1+a/r)\log(6/δ)$ and $n=\lceil Kb_0/s^2\rceil$ have the following property. For the actual TwoBatch outputs $\widehat Z,\widehat H$, with probability at least $1-δ$, writing $H=H_s(σ)$ and $q=2^{-16}$,
--   $$\tfrac34(H+rI_a)\preceq\widehat H+rI_a\preceq\tfrac54(H+rI_a),$$
--   $$\|Φ_σ(\widehat Z)-E\|_⋄≤(s+3s/64)\|H\|_∞+4s\sqrt{qr\|H\|_∞}+qrs.$$
--   On this same event, $\|H\|_∞≤10r$ implies $\|Φ_σ(\widehat Z)-E\|_⋄≤11rs$. Any fixed measurable admissible rank truncation is allowed. This is the full statistical guarantee for the two independent batches.
--
--   Differences from the source:
--   - encoding: finite complex registers and the source conventions → Fin-indexed matrices, explicit positivity and sample-count domains, and the operational definitions in this mission; reason: coordinate and domain conventions preserve every defined physical instance; no statistical guarantee is assumed
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Proposition 3.15, printed p. 30 = PDF p. 30; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

theorem proposition_3_15 : ∃ K : ℝ, 0 < K ∧
    ∀ (a b r : ℕ), 0 < a → 2 ≤ b → 1 ≤ r → r ≤ a*b → a ≤ r*b →
    ∀ (E : Map a b), E ∈ ChanTomoNB.QChan r a b →
    ∀ (σ : Input a), State σ → LE ((1/(2*(a : ℂ))) • 1) σ →
    ∀ s δ : ℝ, 0 < s → s ≤ min 1 (Real.sqrt ((a : ℝ)/r)) → 0 < δ → δ < 1 →
    ∀ (truncate : Joint a b → Joint a b), Measurable truncate →
    (∀ X, X.IsHermitian → IsTruncation r X (truncate X)) →
    let n := batchSize K a b r s δ
    let H := sensitivity E s σ
    let q : ℝ := 2^(-16 : ℤ)
    (pairLaw (outputState E σ) n)
      {z | let out := twoBatch truncate σ s z
        LE ((3/4 : ℂ) • (H+(r : ℂ) • 1)) (out.2+(r : ℂ) • 1) ∧
        LE (out.2+(r : ℂ) • 1) ((5/4 : ℂ) • (H+(r : ℂ) • 1)) ∧
        ChanTomoNB.diamondDist (reconstruct σ out.1) E ≤
          (s+3*s/64)*opNorm H + 4*s*Real.sqrt (q*r*opNorm H) + q*r*s ∧
        (opNorm H ≤ 10*r → ChanTomoNB.diamondDist (reconstruct σ out.1) E ≤ 11*r*s)}
      ≥ ENNReal.ofReal (1-δ) := by sorry

end LowRankIncoherent.Adaptive
