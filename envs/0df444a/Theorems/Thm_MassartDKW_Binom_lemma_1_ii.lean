-- Prove2me | Theorems.Thm_MassartDKW_Binom_lemma_1_ii
-- name    : MassartDKW.Binom.lemma_1_ii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:39.924816+00:00
-- url     : https://prove2.me/theorems/0b485a27-8b44-4e8a-99b5-3bfeedc14294
-- title:
--   Lemma 1(ii), p. 1272 — h(p, ε) ≥ ε²/[2(p + ε/3)(q − ε/3)] + εφ(t)/t, t = ε/(q − ε)
-- statement:
--   Let $0 < \varepsilon \le q = 1 - p < 1$ (so $p > 0$), and let
--
--   $$
--   h(p,\varepsilon) = (p+\varepsilon)\log\frac{p+\varepsilon}{p} + (q-\varepsilon)\log\frac{q-\varepsilon}{q},
--   \qquad
--   \varphi(t) = t - \frac{t^2}{2(1 + 2t/3)} - \log(1+t).
--   $$
--
--   Then, with $t = \varepsilon/(q-\varepsilon)$,
--
--   $$
--   h(p,\varepsilon) \;\ge\; \frac{\varepsilon^2}{2\,(p + \varepsilon/3)(q - \varepsilon/3)} + \frac{\varepsilon\,\varphi(t)}{t}.
--   $$
--
--   When $\varepsilon = q$ the parameter $t$ is $+\infty$, and the term $\varepsilon\varphi(t)/t$ is read as its limit $\varepsilon/4$ (Lemma 1(i)); the inequality then reads $h(p,q) \ge q^2/[2(p+q/3)(2q/3)] + q/4$.
--
--   This is part (ii) of Massart's Lemma 1: a lower bound for the Cramér transform of the Bernoulli law that sharpens the classical quadratic (Bernstein-type) bound. Combined with the Cramér–Chernoff bound (Comment 3) and $\varphi \ge 0$ it yields the binomial tail inequality of Theorem 2; in the paper it is also an ingredient of Proposition 1.
--
--   **Formalization Note.** The statement is split into the two cases $\varepsilon < q$, where $t = \varepsilon/(q - \varepsilon)$ is a real number, and $\varepsilon = q$, where the correction term takes its limiting value $\varepsilon/4$. Without the split, Lean's convention $x/0 = 0$ would turn the case $\varepsilon = q$ into the weaker claim with correction term $0$. The page's hypothesis $q < 1$ is $p > 0$; $q$ is written out as $1 - p$.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1272, Lemma 1(ii)

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1(ii), p. 1272: for `0 < ε ≤ q = 1 − p < 1`,
`h(p, ε) ≥ ε²/[2(p + ε/3)(q − ε/3)] + εφ(t)/t` with `t = ε/(q − ε)`.
For `ε < q` the term `εφ(t)/t` is evaluated at the real number `t = ε/(q − ε)`; at `ε = q`
(`t = ∞`) it takes its limiting value `ε/4` (Lemma 1(i)). -/
theorem lemma_1_ii (p ε : ℝ) (hp : 0 < p) (hε : 0 < ε) (hεq : ε ≤ 1 - p) :
    (ε < 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3))
          + ε * phi (ε / (1 - p - ε)) / (ε / (1 - p - ε)) ≤ h p ε) ∧
    (ε = 1 - p →
      ε ^ 2 / (2 * (p + ε / 3) * (1 - p - ε / 3)) + ε / 4 ≤ h p ε) := by sorry

end MassartDKW.Binom
