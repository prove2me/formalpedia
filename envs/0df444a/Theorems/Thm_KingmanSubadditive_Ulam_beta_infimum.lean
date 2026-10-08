-- Prove2me | Theorems.Thm_KingmanSubadditive_Ulam_beta_infimum
-- name    : KingmanSubadditive.Ulam.beta_infimum
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:46:28.331626+00:00
-- url     : https://prove2.me/theorems/d20ae592-8b8e-4844-9ea7-eef380c1cf67
-- title:
--   Proof of Theorem 8, p. 896 — the infimum of the β admitting some α with (2.4.8) is δ^½ + δ^{−½}
-- statement:
--   The equation $\log(1+\delta)=\dfrac{2\delta}{1+\delta}$ has a unique positive root $\delta$, and
--   $$\inf\Big\{\,b>0\ :\ \exists\,\alpha\in(0,b),\ 2\alpha+(b-\alpha)\log(b-\alpha)-\alpha\log\alpha-b\log b<0\,\Big\}=\delta^{1/2}+\delta^{-1/2}.$$
--
--   Together with (2.4.8), this identifies the best upper bound on the Ulam constant that the first-moment bound (2.4.7) yields: $c\le\delta^{1/2}+\delta^{-1/2}$.
--
--   **Formalization Note** The admissible set is nonempty and bounded below by $0$, so the real infimum is the true one. The paper's $\beta$ is written $b$ for the free parameter.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 896, §2.4, proof of Theorem 8

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

namespace KingmanSubadditive.Ulam

/-- The optimisation at the end of the proof of Theorem 8 (Kingman, *Subadditive ergodic theory*,
Ann. Probab. 1(6):883–899 (1973), §2.4, p. 896): the infimum of the values `b > 0` for which some
`α ∈ (0, b)` satisfies (2.4.8), `2α + (b − α) log (b − α) − α log α − b log b < 0`, is
`β = δ^½ + δ^{−½}`, where `δ` is the unique positive root of `log (1 + δ) = 2δ/(1 + δ)`.

**Formalization Note** The first conjunct asserts that the positive root exists and is unique,
so the second is not vacuous. The set of admissible `b` is nonempty and bounded below by `0`, so
the real `sInf` is the true infimum. -/
theorem beta_infimum :
    (∃! δ : ℝ, 0 < δ ∧ Real.log (1 + δ) = 2 * δ / (1 + δ)) ∧
    ∀ δ : ℝ, 0 < δ → Real.log (1 + δ) = 2 * δ / (1 + δ) →
      sInf {b : ℝ | 0 < b ∧ ∃ α : ℝ, 0 < α ∧ α < b ∧ stirlingExponent α b < 0} =
        Real.sqrt δ + 1 / Real.sqrt δ := by sorry

end KingmanSubadditive.Ulam
