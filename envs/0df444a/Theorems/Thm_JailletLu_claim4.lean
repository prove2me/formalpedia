-- Prove2me | Theorems.Thm_JailletLu_claim4
-- name    : JailletLu.claim4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:33:36.09497+00:00
-- url     : https://prove2.me/theorems/00bf1582-efd5-4531-a721-156092e3ccfa
-- title:
--   Claim 4 (corrected: $n\ge 2929$): $R(f,\beta,s)\ge 0.706$
-- statement:
--   Let $n\ge 2929$ be an integer and $f,\beta,s$ reals with
--   $$
--   1\ \ge\ f\ >\ 0,\qquad f\ \ge\ s\ \ge\ \beta\ \ge\ 0,\qquad \beta=0\Rightarrow s=0,\qquad f-s\ \le\ (1-\ln 2)+\frac1n .
--   $$
--   Then
--   $$
--   R(f,\beta,s)\ \ge\ 0.706 .
--   $$
--   With $f=f_a$, $\beta=\beta_a$, $s=s_a$ the constraints are those satisfied by every advertiser (the paragraph before Claim 4), so the ratio bound of §5.4 follows.
--
--   The paper states this "for $n\ge 100$", which is false: at $n=100$ the point $(f,\beta,s)=(1,\ \ln 2-\tfrac1{100},\ \ln 2-\tfrac1{100})$ satisfies every constraint and $R=1-e^{-1}+e^{-1}g(1,\ln2-\tfrac1{100})\approx 0.705433$. Numerically, $\min_\beta R(1,\beta,\ln 2-\tfrac1n)$ is $\approx 0.7059999921$ at $n=2928$ and $\approx 0.7060000017$ at $n=2929$, so $2929$ is the sharp threshold.
--
--   Differences from the source:
--   - correction: for n ≥ 100 → for n ≥ 2929; reason: false at n = 100: (f, β, s) = (1, ln 2 − 1/100, ln 2 − 1/100) meets every constraint and R ≈ 0.705433 < 0.706; min_β R(1, β, ln 2 − 1/n) ≈ 0.7059999921 at n = 2928 and ≈ 0.7060000017 at n = 2929 (planning_numerics/check_claim4.py), so 2929 is sharp
--   - encoding: R(f_a, β_a, s_a) with quotients 1/f_a and s_a/β_a → hypotheses f > 0 and β = 0 → s = 0; reason: they exclude exactly the points where the printed quotients are undefined; in the model β_a = 0 forces s_a = 0
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, Claim 4, p. 16

import Mathlib
import Definitions.Def_JailletLu_R

namespace JailletLu

/-- **Claim 4 (corrected: n ≥ 2929).**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 16: "We can numerically show that, for n ≥ 100: Claim 4. Subject to
1 ≥ f_a ≥ s_a ≥ β_a ≥ 0 and f_a − s_a ≤ (1 − ln 2) + 1/n, R(f_a, β_a, s_a) ≥ 0.706."

Conclusion: for every integer `n ≥ 2929` and reals `f, β, s` with `1 ≥ f > 0`, `f ≥ s ≥ β ≥ 0`,
`β = 0 → s = 0` and `f − s ≤ (1 − ln 2) + 1/n`, `R(f, β, s) ≥ 0.706`.

**Formalization Note.** *Correction.* The printed range `n ≥ 100` is false: at `n = 100` the point
`(f, β, s) = (1, ln 2 − 1/100, ln 2 − 1/100)` satisfies every constraint and
`R = 1 − 1/e + g(1, s)/e ≈ 0.705433 < 0.706`; the minimum over `β` of `R(1, β, ln 2 − 1/n)` is
`≈ 0.7059999921` at `n = 2928` and `≈ 0.7060000017` at `n = 2929`, so `2929` is the sharp threshold
(numerical evidence, `planning_numerics/check_claim4.py`). The paper's reported minimizer
`f ∈ [0.999, 1]`, `s ∈ [0.692, 0.693]`, `β ∈ [0.564, 0.565]` is the `n → ∞` one. *Encoding.*
`f > 0` and `β = 0 → s = 0` exclude exactly the points where `R`'s quotients `1/f` and `s/β` are
undefined; in the model `β_a = 0` forces `s_a = 0`. -/
theorem claim4 (n : ℕ) (hn : 2929 ≤ n) (f β s : ℝ) (hf0 : 0 < f) (hf1 : f ≤ 1) (hβ0 : 0 ≤ β)
    (hβs : β ≤ s) (hsf : s ≤ f) (hβs0 : β = 0 → s = 0)
    (hgap : f - s ≤ (1 - Real.log 2) + 1 / (n : ℝ)) :
    (0.706 : ℝ) ≤ R f β s := by sorry

end JailletLu
