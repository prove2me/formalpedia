-- Prove2me | Theorems.Thm_KendallBD_Sol_genFun_hasSum
-- name    : KendallBD.Sol.genFun_hasSum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:25:19.743262+00:00
-- url     : https://prove2.me/theorems/9f49c2d5-fde9-4fd0-8849-bc31240b06a9
-- title:
--   §2, (8)–(9), p. 3 — generating function of the geometric law
-- statement:
--   For continuous, nonnegative birth and death rates $\lambda,\mu$ and every $t\ge0$, let $P_n(t)$, $\xi_t$, and $\eta_t$ have Kendall’s definitions. For every real $z$ with $|z|\le1$,
--   $$
--   \sum_{n=0}^{\infty}P_n(t)z^n=\frac{\xi_t+(1-\xi_t-\eta_t)z}{1-\eta_t z}.
--   $$
--   This identifies the generating function in equation (9) with the distribution in equation (8).
--
--   **Formalization Note** The series is stated with `HasSum`; its domain is the real interval $[-1,1]$. Rate continuity on $\mathbb R$ makes the oriented integrals well behaved, while only nonnegative time is used.
-- source:
--   Kendall, On the generalized "birth-and-death" process, Ann. Math. Statist. 19 (1948), §2, (8)–(9), p. 3

import Mathlib
import Definitions.Def_KendallBD_Sol_Setting

open Filter
open scoped Topology

namespace KendallBD.Sol

theorem genFun_hasSum (lam mu : ℝ → ℝ) (hlam : Continuous lam) (hmu : Continuous mu)
    (hlam0 : ∀ t, 0 ≤ t → 0 ≤ lam t) (hmu0 : ∀ t, 0 ≤ t → 0 ≤ mu t) :
    ∀ t, 0 ≤ t → ∀ z : ℝ, |z| ≤ 1 →
      HasSum (fun n : ℕ => P lam mu n t * z ^ n)
        (genFun (xi lam mu t) (eta lam mu t) z) := by sorry

end KendallBD.Sol
