-- Prove2me | Theorems.Thm_KalaiVempala_Lazy_fll_star_law_eq
-- name    : KalaiVempala.Lazy.fll_star_law_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T08:44:15.041213+00:00
-- url     : https://prove2.me/theorems/192a75fe-332b-490b-afd4-92d0b303e543
-- title:
--   Proof of Lemma 1.2 (FLL* case), p. 304 — p_t ∼ μ for every period t
-- statement:
--   **The perturbation of FLL\* is always Laplace distributed.** Let $\varepsilon > 0$ and let $s_1, s_2, \dots \in \mathbb R^n$ be any fixed state sequence. Let $\nu_t$ be the law of the perturbation $p_t$ of FLL\*($\varepsilon$): $p_1 \sim \mu$, and $p_{t+1}$ is obtained from $p_t$ and $s_t$ by the FLL\* update (accept $p_t - s_t$ with probability $\min\{1, d\mu(p_t - s_t)/d\mu(p_t)\}$, otherwise take $-p_t$). Then for every $t \ge 1$,
--
--   $$\nu_t = \mu, \qquad d\mu(x) = (\varepsilon/2)^n e^{-\varepsilon |x|_1}.$$
--
--   Consequently FLL\*($\varepsilon$), which plays $M(s_{1:t-1} + p_t)$ on period $t$, has on every period the same expected cost as FPL\*($\varepsilon$).
--
--   **Formalization Note** $\nu_t$ is `fllStarLaw ε s t`, defined by the recursion $\nu_1 = \mu$, $\nu_{t+1}$ = second marginal of `fllStarJoint ε (s t) ν_t`. Index $0$ is unused.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 304, proof of Lemma 1.2 (FLL* case), first paragraph (induction on t)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Lazy_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Lazy

theorem fll_star_law_eq {n : ℕ} (ε : ℝ) (hε : 0 < ε) (s : ℕ → Fin n → ℝ) :
    ∀ t, 1 ≤ t → fllStarLaw ε s t = KalaiVempala.Multiplicative.laplaceLaw n ε := by sorry

end KalaiVempala.Lazy
