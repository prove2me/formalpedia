-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_8
-- name    : MeanOnlyProphet.lemma_A_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:26.761739+00:00
-- url     : https://prove2.me/theorems/04108d01-c209-454e-8c0b-6e028633b7c6
-- title:
--   Lemma A.8 — $\mathcal E\ge(1-\overline P(1))/\big(n(1+\sqrt{1+e^{-\Lambda/n}})\big)$
-- statement:
--   Let $n\ge2$ and let $q$ be a bounded, nonnegative, nondecreasing step function on $[0,1]$ with finitely many jumps, right-continuous on $[0,1)$ with $q(1)=q(1^-)$, and with $q(t)=\Lambda>0$ for $t\in[1-\frac1n,1]$.
--   Then
--   $$
--   \mathcal E\ \ge\ \frac{1-\overline P(1)}{n\left(1+\sqrt{1+e^{-\Lambda/n}}\right)} .
--   $$
--   It is the lower bound on $\mathcal E=A_P(0)-A(0)$ against which Lemma A.6's upper bound is compared.
--
--   Differences from the source:
--   - encoding: bounded, nonnegative, nondecreasing step function with finitely many jumps, right-continuous on [0,1), q(1) = q(1⁻) → IsStepRate q: nonnegative and monotone on [0,1] with finitely many values there, right-continuous on [0,1), left-continuous at 1; reason: for a nondecreasing function, finitely many values on [0,1] is the same as a step function with finitely many jumps, and implies boundedness
--   - encoding: q(t) = Λ > 0 on [1 − 1/n, 1] → a real Λ > 0 with q t = Λ for t ∈ [1 − 1/n, 1]; reason: 1 − 1/n computed in ℝ
--   - encoding: a real rate q → the extended rate toRate q (t ↦ ENNReal.ofReal (q t)) fed to the ℝ≥0∞-valued functionals; reason: q ≥ 0 on [0,1], so the values are unchanged; one set of definitions serves real and extended rates
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.8, p.34 (PDF p.35)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tn
import Definitions.Def_MeanOnlyProphet_IsStepRate

namespace MeanOnlyProphet

/-- **Lemma A.8.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.8, p.34 (PDF p.35): "We have ℰ ≥ (1 − P̄(1)) / (n · (1 + √(1 +
e^{−Λ/n})))."

Standing context (p.30 and p.32): `n ≥ 2`; `q` a bounded, nonnegative, nondecreasing step function with
finitely many jumps, right-continuous on `[0,1)`, `q(1) = q(1⁻)` (`IsStepRate`), and `q(t) = Λ > 0` for
`t ∈ [1 − 1/n, 1]`.

**Formalization Note.** The real rate `q` enters the functionals as `toRate q`; `P̄(1)` is `Pbar n _ 1`. -/
theorem lemma_A_8 (n : ℕ) (hn : 2 ≤ n) (q : ℝ → ℝ) (hq : IsStepRate q) (Λ : ℝ) (hΛ : 0 < Λ)
    (hqΛ : ∀ t ∈ Set.Icc (1 - 1 / (n : ℝ)) 1, q t = Λ) :
    (1 - Pbar n (toRate q) 1) / (n * (1 + Real.sqrt (1 + Real.exp (-Λ / n)))) ≤
      Ecal n (toRate q) := by sorry

end MeanOnlyProphet
