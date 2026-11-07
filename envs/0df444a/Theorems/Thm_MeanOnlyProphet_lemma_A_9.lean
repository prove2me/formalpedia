-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_9
-- name    : MeanOnlyProphet.lemma_A_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:27:11.713006+00:00
-- url     : https://prove2.me/theorems/31dc76b8-00c9-42e5-9d41-17676978dadc
-- title:
--   Lemma A.9 — comparison of Lemmas A.6 and A.8 with constant $9/64$
-- statement:
--   Let $n\ge2$ and let $q$ be a bounded, nonnegative, nondecreasing step function on $[0,1]$ with finitely many jumps, right-continuous on $[0,1)$ with $q(1)=q(1^-)$, and with $q(t)=\Lambda>0$ for $t\in[1-\frac1n,1]$. Write $z=\Lambda/n$. Then
--   $$
--   n\left(1+\sqrt{1+e^{-z}}\right)\cdot\frac{\int_0^1q(t)\,dt}{\Lambda}\cdot\frac{\overline P(1)-S(1)}{1-\overline P(1)}\ \le\ \frac9{64}.
--   $$
--   Combined with Lemmas A.6 and A.8 it gives $\int_0^1D_n^+\le\frac9{64}\mathcal E$ for step rates.
--
--   Differences from the source:
--   - encoding: bounded, nonnegative, nondecreasing step function with finitely many jumps, right-continuous on [0,1), q(1) = q(1⁻) → IsStepRate q: nonnegative and monotone on [0,1] with finitely many values there, right-continuous on [0,1), left-continuous at 1; reason: for a nondecreasing function, finitely many values on [0,1] is the same as a step function with finitely many jumps, and implies boundedness
--   - encoding: q(t) = Λ > 0 on [1 − 1/n, 1] → a real Λ > 0 with q t = Λ for t ∈ [1 − 1/n, 1]; reason: 1 − 1/n computed in ℝ
--   - encoding: a real rate q → the extended rate toRate q (t ↦ ENNReal.ofReal (q t)) fed to the ℝ≥0∞-valued functionals; reason: q ≥ 0 on [0,1], so the values are unchanged; one set of definitions serves real and extended rates
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.9, p.35 (PDF p.36)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tn
import Definitions.Def_MeanOnlyProphet_IsStepRate

namespace MeanOnlyProphet

/-- **Lemma A.9.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.9, p.35 (PDF p.36): "In the following lemma, we denote z = Λ/n and
x = e^{−z} ∈ (0, 1) for simplicity. Lemma A.9. We have n · (1 + √(1 + e^{−z})) · (∫_0^1 q(t) dt / Λ) ·
(P̄(1) − S(1))/(1 − P̄(1)) ≤ 9/64."

Standing context (p.30 and p.32): `n ≥ 2`; `q` a bounded, nonnegative, nondecreasing step function with
finitely many jumps, right-continuous on `[0,1)`, `q(1) = q(1⁻)` (`IsStepRate`), and `q(t) = Λ > 0` for
`t ∈ [1 − 1/n, 1]`.

**Formalization Note.** The real rate `q` enters the functionals as `toRate q`; `P̄(1)` is `Pbar n _ 1`,
`S(1)` is `survS _ 1`; `1 − P̄(1) > 0` on this class (the proof shows `P̄(1) ≤ e^{−z} < 1`). -/
theorem lemma_A_9 (n : ℕ) (hn : 2 ≤ n) (q : ℝ → ℝ) (hq : IsStepRate q) (Λ : ℝ) (hΛ : 0 < Λ)
    (hqΛ : ∀ t ∈ Set.Icc (1 - 1 / (n : ℝ)) 1, q t = Λ) :
    let z := Λ / n
    n * (1 + Real.sqrt (1 + Real.exp (-z))) * ((∫ t in (0 : ℝ)..1, q t) / Λ) *
        ((Pbar n (toRate q) 1 - survS (toRate q) 1) / (1 - Pbar n (toRate q) 1)) ≤ 9 / 64 := by sorry

end MeanOnlyProphet
