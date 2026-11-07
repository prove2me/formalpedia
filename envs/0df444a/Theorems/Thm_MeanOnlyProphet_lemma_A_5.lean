-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_5
-- name    : MeanOnlyProphet.lemma_A_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:12.648219+00:00
-- url     : https://prove2.me/theorems/937ca6a0-94b6-4541-8866-6b5a48aab8ba
-- title:
--   Lemma A.5 — capping the rate at $q(1-1/n)$
-- statement:
--   Let $n\ge2$ and let $q$ be a bounded, nonnegative, nondecreasing step function on $[0,1]$ with finitely many jumps, right-continuous on $[0,1)$ with $q(1)=q(1^-)$. Let $q_*(t)=\min\{q(t),q(1-\frac1n)\}$ and mark with $*$ the quantities computed from $q_*$. Then
--   1. $P(t)=P_*(t)$ for every $t\in[0,1]$;
--   2. $\mathcal E\ge\mathcal E_*$;
--   3. $D_n(t)\le D_{n,*}(t)$ for almost every $t\in[0,1]$.
--
--   It lets the proof of Lemma A.4 assume the rate is constant on the last interval $[1-\frac1n,1]$.
--
--   Differences from the source:
--   - encoding: bounded, nonnegative, nondecreasing step function with finitely many jumps, right-continuous on [0,1), q(1) = q(1⁻) → IsStepRate q: nonnegative and monotone on [0,1] with finitely many values there, right-continuous on [0,1), left-continuous at 1; reason: for a nondecreasing function, finitely many values on [0,1] is the same as a step function with finitely many jumps, and implies boundedness
--   - encoding: a real rate q → the extended rate toRate q (t ↦ ENNReal.ofReal (q t)) fed to the ℝ≥0∞-valued functionals; reason: q ≥ 0 on [0,1], so the values are unchanged; one set of definitions serves real and extended rates
--   - encoding: for almost every t ∈ [0,1] → ∀ᵐ t ∂(volume.restrict (Icc 0 1)); reason: Lebesgue measure on [0,1]
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.5, p.31 (PDF p.32); standing assumptions p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tn
import Definitions.Def_MeanOnlyProphet_IsStepRate

open MeasureTheory

namespace MeanOnlyProphet

/-- **Lemma A.5.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.5, p.31 (PDF p.32): "Let q∗(t) = min{q(t), q(1 − 1/n)}. Throughout
this lemma and its proof, let the starred quantities be obtained by replacing q with q∗ in all
definitions that depend on q. Then P(t) = P∗(t) for every t ∈ [0, 1], ℰ ≥ ℰ∗, and Dn(t) ≤ Dn,∗(t) for
almost every t ∈ [0, 1]."

Standing context (proof of Lemma A.4, p.30): `n ≥ 2` and `q` a bounded, nonnegative, nondecreasing step
function with finitely many jumps, right-continuous on `[0,1)`, with `q(1) = q(1⁻)` (`IsStepRate`).

**Formalization Note.** The real rates `q` and `q∗` enter the functionals as `toRate`. `P` is the
unbarred `P(t)` of p.28. "Almost every" is with respect to Lebesgue measure on `[0,1]`. -/
theorem lemma_A_5 (n : ℕ) (hn : 2 ≤ n) (q : ℝ → ℝ) (hq : IsStepRate q) :
    let qs : ℝ → ℝ := fun t => min (q t) (q (1 - 1 / (n : ℝ)))
    (∀ t ∈ Set.Icc (0 : ℝ) 1, Pfun n (toRate q) t = Pfun n (toRate qs) t) ∧
      Ecal n (toRate qs) ≤ Ecal n (toRate q) ∧
      ∀ᵐ t ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), Dn n (toRate q) t ≤ Dn n (toRate qs) t := by sorry

end MeanOnlyProphet
