-- Prove2me | Theorems.Thm_MeanOnlyProphet_lemma_A_4
-- name    : MeanOnlyProphet.lemma_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:26:36.892049+00:00
-- url     : https://prove2.me/theorems/927a8d87-2bda-4f96-b774-e26ee13c0d6e
-- title:
--   Lemma A.4 — $\int_0^1 D_n(t)^+\,dt\le\frac9{64}\,\mathcal E$
-- statement:
--   Let $n\ge2$ and let $q$ be a nonnegative, nondecreasing function on $[0,1]$, possibly taking the value $+\infty$, with the conventions $e^{-\infty}=0$ and $q(t)\cdot A(t)=0$ whenever $q(t)=+\infty$. Then
--   $$
--   \int_0^1 D_n(t)^+\,dt\ \le\ \frac9{64}\cdot\mathcal E. \tag{A.3}
--   $$
--   With $\theta(0)+\frac9{64}b_{40}<1$ this gives $J_n(b,q)\ge L(b,q)$ for every rate, which transfers the asymptotic guarantee to every finite $n$; it applies to the input rate $r(t)=-n\log F(\theta(t))$, which may be infinite.
--
--   Differences from the source:
--   - encoding: q nonnegative, nondecreasing on [0,1], possibly +∞ → q : ℝ → ℝ≥0∞ with MonotoneOn q on [0,1]; reason: ℝ≥0∞ values are nonnegative; the conventions are built into eNeg and qTimesA
--   - encoding: D_n(t)^+ → max (Dn n q t) 0; reason: notation
-- source:
--   Feng, Jin, Wu, Xiang, Mean-only Prophet Inequalities, arXiv:2610.24711 (held version, sha256 c68bfec4…74e93a), Lemma A.4, (A.3), p.30 (PDF p.31)

import Mathlib
import Definitions.Def_MeanOnlyProphet_Tn

namespace MeanOnlyProphet

/-- **Lemma A.4.** Feng, Jin, Wu, Xiang, *Mean-only Prophet Inequalities*, arXiv:2610.24711 (held
version, sha256 c68bfec4…), Lemma A.4, (A.3), p.30 (PDF p.31): "Let n ≥ 2, and let q be a nonnegative,
nondecreasing function on [0, 1]. Use the conventions e^{−∞} = 0 and q(t) · A(t) = 0 whenever q(t) = +∞.
Then ∫_0^1 Dn(t)^+ dt ≤ (9/64) · ℰ."

**Formalization Note.** `q : ℝ → ℝ≥0∞` is nondecreasing on `[0,1]` and may take the value `+∞`
(nonnegativity is automatic); it is not assumed bounded or a step function. The conventions are built
into `eNeg` (`e^{−∞} = 0`) and `qTimesA` (`q · A = 0` at `q = +∞`). `D_n(t)^+` is `max (Dn n q t) 0`. -/
theorem lemma_A_4 (n : ℕ) (hn : 2 ≤ n) (q : ℝ → ENNReal) (hq : MonotoneOn q (Set.Icc 0 1)) :
    ∫ t in (0 : ℝ)..1, max (Dn n q t) 0 ≤ 9 / 64 * Ecal n q := by sorry

end MeanOnlyProphet
