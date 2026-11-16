-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_B_4
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_B_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:10:05.335192+00:00
-- url     : https://prove2.me/theorems/8bb74235-78f3-4bd1-bc0e-fda4e6e3327f
-- title:
--   Theorem B.4 — detection on the complete graph
-- statement:
--   Let $G=K_n$, $y=c\mathbf 1$, $1\le b<n$, $\tau>0$ and $s_\tau=\lceil n\tau/L\rceil$. If $s_\tau>b$ there are no alternatives. If $1\le s_\tau\le b<n$, then for $0\le q\le n$
--   $$\beta^{\mathrm{imp}}_q(c\mathbf 1,\tau)=\binom{n-s_\tau}{q}\Big/\binom nq=\binom{n-q}{s_\tau}\Big/\binom n{s_\tau},$$
--   with binomial coefficients equal to $0$ when the lower argument exceeds the upper one. A uniformly random $q$-set attains this value, and deterministic detection needs exactly $n-s_\tau+1$ audits. For $0<\delta<1$, the least $q$ with miss probability at most $\delta$ satisfies
--   $$q^*_\delta\le\min\{n-s_\tau+1,\ \lceil (n/s_\tau)\log(1/\delta)\rceil\}.$$
--
--   Differences from the source:
--   - encoding: randomized adaptive detectors → probability mass functions over deterministic adaptive strategies; reason: private randomness drawn before the run; finite distributions are included
--   - encoding: the least q with miss probability at most δ → the infimum over all natural q; reason: q > n behaves as q = n, so the least such q is unchanged
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem B.4, printed p.25 (PDF p.27), proof printed p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_Detection

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem B.4, printed p.25 / PDF p.27 (proof p.26 / PDF p.28). `G = K_n`, `y = c1`,
`1 ≤ b < n`, `τ > 0`, `s_τ = ⌈nτ/L⌉`. If `s_τ > b` there are no alternatives. If
`1 ≤ s_τ ≤ b < n`, then for `0 ≤ q ≤ n`,
`β^imp_q(c1, τ) = C(n − s_τ, q)/C(n, q) = C(n − q, s_τ)/C(n, s_τ)` (binomials `0` when the lower
argument exceeds the upper), a uniformly random `q`-set attains it, deterministic detection
needs exactly `n − s_τ + 1` audits, and for `0 < δ < 1` the least `q` with miss probability at
most `δ` is at most `min{n − s_τ + 1, ⌈(n/s_τ) log(1/δ)⌉}`. -/
theorem theorem_B_4 (n b : ℕ) (L τ c : ℝ) (hL : 0 < L) (hτ : 0 < τ) (hb1 : 1 ≤ b)
    (hbn : b < n) :
    (b < ⌈n * τ / L⌉₊ → impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c) = ∅) ∧
    (1 ≤ ⌈n * τ / L⌉₊ → ⌈n * τ / L⌉₊ ≤ b →
      (∀ q : ℕ, q ≤ n →
        optMiss q (fun _ => c) (impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c)) =
          ((n - ⌈n * τ / L⌉₊).choose q : ENNReal) / (n.choose q : ENNReal) ∧
        ((n - ⌈n * τ / L⌉₊).choose q : ENNReal) / (n.choose q : ENNReal) =
          ((n - q).choose ⌈n * τ / L⌉₊ : ENNReal) / (n.choose ⌈n * τ / L⌉₊ : ENNReal) ∧
        ∀ hq : q ≤ n, NoFalseAlarm (setPolicy (uniformQSet n q hq) (fun _ => c)) q (fun _ => c) ∧
          (⨆ x ∈ impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c),
              missProb (setPolicy (uniformQSet n q hq) (fun _ => c)) q x) =
            optMiss q (fun _ => c) (impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c))) ∧
      detAudits (fun _ => c) (impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c)) =
        n - ⌈n * τ / L⌉₊ + 1 ∧
      ∀ δ : ℝ, 0 < δ → δ < 1 →
        sInf {q : ℕ | optMiss q (fun _ => c)
            (impactAlt (⊤ : SimpleGraph (Fin n)) L b τ (fun _ => c)) ≤ ENNReal.ofReal δ} ≤
          min (n - ⌈n * τ / L⌉₊ + 1) ⌈(n / (⌈n * τ / L⌉₊ : ℝ)) * Real.log (1 / δ)⌉₊) := by sorry

end MeanCertificates1424.Hardness.Supplement
