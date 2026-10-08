-- Prove2me | Theorems.Thm_MassartDKW_Binom_lemma_1_i
-- name    : MassartDKW.Binom.lemma_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:45.799805+00:00
-- url     : https://prove2.me/theorems/4d7c0657-5d27-4d5d-9760-5b093ff8970c
-- title:
--   Lemma 1(i), p. 1272 — φ is positive, increasing and convex with φ(t)/t → 1/4
-- statement:
--   Let
--
--   $$
--   \varphi(t) = t - \frac{t^2}{2\,(1 + 2t/3)} - \log(1+t), \qquad t \ge 0.
--   $$
--
--   Then $\varphi$ is a positive increasing convex function on $[0,\infty)$, and
--
--   $$
--   \lim_{t\to\infty} \frac{\varphi(t)}{t} = \frac14 .
--   $$
--
--   Precisely: $\varphi(t) > 0$ for every $t > 0$; $\varphi$ is strictly increasing on $[0,\infty)$; $\varphi$ is convex on $[0,\infty)$; and $\varphi(t)/t \to 1/4$ as $t \to \infty$.
--
--   This is part (i) of Massart's Lemma 1, a lower bound for the Cramér transform of the Bernoulli law. The nonnegativity of $\varphi$ is what turns Lemma 1(ii) into the explicit binomial tail bound of Theorem 2, and the limit $1/4$ gives the value of the correction term $\varepsilon\varphi(t)/t$ at $\varepsilon = q$.
--
--   **Formalization Note.** The paper says "positive"; since $\varphi(0) = 0$ (the paper's own proof starts from this), positivity is stated for $t > 0$. Monotonicity is stated as strict monotonicity on $[0,\infty)$, as the paper's proof gives ($\varphi' > 0$ for $t > 0$).
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1272, Lemma 1(i)

import Mathlib
import Definitions.Def_MassartDKW_Binom_Setting

namespace MassartDKW.Binom

/-- Massart (1990), Lemma 1(i), p. 1272: `φ` is a positive (for `t > 0`; `φ(0) = 0`), increasing,
convex function on `[0, ∞)` with `φ(t)/t → 1/4` as `t → ∞`. -/
theorem lemma_1_i :
    (∀ t : ℝ, 0 < t → 0 < phi t) ∧
    StrictMonoOn phi (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) phi ∧
    Filter.Tendsto (fun t => phi t / t) Filter.atTop (nhds (1 / 4)) := by sorry

end MassartDKW.Binom
