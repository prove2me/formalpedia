-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_6
-- name    : MeanOnlyProphet.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:57.985091+00:00
-- url     : https://prove2.me/theorems/fff89e3c-2e8f-4810-98ce-10d8ffa520ff
-- title:
--   Lemma A.6 — $D_n(t)\le \frac{q(t)}{\Lambda}(\overline P(1)-S(1))$
-- statement:
--   Let $n\ge2$ and let $q$ be a bounded, nonnegative, nondecreasing step function on $[0,1]$ with finitely many jumps, right-continuous on $[0,1)$ with $q(1)=q(1^-)$, and with $q(t)=\Lambda>0$ for $t\in[1-\frac1n,1]$.
--   Then for almost every $t\in[0,1]$,
--   $$
--   D_n(t)\ \le\ \frac{q(t)}{\Lambda}\Big(\overline P(1)-S(1)\Big).
--   $$
--   Integrating gives $\int_0^1D_n^+\le\frac{\overline P(1)-S(1)}{\Lambda}\int_0^1q$, the first half of the proof of Lemma A.4.
--
--   Differences from the source:
--   - encoding: bounded, nonnegative, nondecreasing step function with finitely many jumps, right-continuous on [0,1), q(1) = q(1⁻) → IsStepRate q: nonnegative and monotone on [0,1] with finitely many values there, right-continuous on [0,1), left-continuous at 1; reason: for a nondecreasing function, finitely many values on [0,1] is the same as a step function with finitely many jumps, and implies boundedness
--   - encoding: q(t) = Λ > 0 on [1 − 1/n, 1] → a real Λ > 0 with q t = Λ for t ∈ [1 − 1/n, 1]; reason: 1 − 1/n computed in ℝ
--   - encoding: a real rate q → the extended rate toRate q (t ↦ ENNReal.ofReal (q t)) fed to the ℝ≥0∞-valued functionals; reason: q ≥ 0 on [0,1], so the values are unchanged; one set of definitions serves real and extended rates
--   - encoding: for almost every t ∈ [0,1] → ∀ᵐ t ∂(volume.restrict (Icc 0 1)); reason: Lebesgue measure on [0,1]
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.6, p.32 (PDF p.33)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tn
import Definitions.Def_MeanOnlyProphet_IsStepRate

open MeasureTheory

namespace MeanOnlyProphet

/-- **Lemma A.6.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.6, p.32 (PDF p.33), with the assumptions stated just before it:
"we now assume that q is a bounded, nonnegative, nondecreasing step function with finitely many jumps,
and satisfies q(t) = Λ > 0 for t ∈ [1 − 1/n, 1]. … Lemma A.6. For almost every t ∈ [0, 1], we have Dn(t)
≤ (q(t)/Λ) · (P̄(1) − S(1))."

Standing context (proof of Lemma A.4, p.30): `n ≥ 2`, `q` right-continuous on `[0,1)` with
`q(1) = q(1⁻)` (`IsStepRate`).

**Formalization Note.** The real rate `q` enters the functionals as `toRate q`; `P̄(1)` is `Pbar n _ 1`
and `S(1)` is `survS _ 1`. "Almost every" is with respect to Lebesgue measure on `[0,1]`. -/
theorem lemma_A_6 (n : ℕ) (hn : 2 ≤ n) (q : ℝ → ℝ) (hq : IsStepRate q) (Λ : ℝ) (hΛ : 0 < Λ)
    (hqΛ : ∀ t ∈ Set.Icc (1 - 1 / (n : ℝ)) 1, q t = Λ) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      Dn n (toRate q) t ≤ q t / Λ * (Pbar n (toRate q) 1 - survS (toRate q) 1) := by sorry

end MeanOnlyProphet
