-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_user_problem_convex
-- name    : OffloadGNEP.Exist.user_problem_convex
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:40.201962+00:00
-- url     : https://prove2.me/theorems/73c996d0-9bdf-4eef-8aa2-38bbdbad8e37
-- title:
--   p. 11 — under Assumption A each user's problem is convex for fixed values of the other users' variables
-- statement:
--   Assume Assumption A and the standing hypotheses. Fix a user $u$ and the other users' strategies $x_{-u}$ (arbitrary real vectors). Then user $u$'s feasible set
--   $$X_u(x_{-u})=\{y\in\tilde K_u:\ (y,x_{-u})\in\Omega\}$$
--   is convex, and the cost $y\mapsto\lambda_uR_u(y,x_{-u})$ is a convex function on $X_u(x_{-u})$.
--
--   Convexity of every player's problem in its own variables, together with the shared linear constraint, is what makes (10)–(15) a jointly convex GNEP, whose variational solutions are equilibria.
--
--   **Formalization Note** The others' block $x_{-u}$ is not required to lie in $\prod_{v\ne u}\tilde K_v$; on $X_u(x_{-u})$ both denominators of the cost are positive under Assumption A.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 11, "each user's problem is convex for given values of the other users' variables"

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- p. 11: under Assumption A each user's problem is convex for given values of the other users'
variables. For every user `u` and every profile `x` (only `x_{-u}` matters), the feasible set
`{y ∈ K̃_u : (y, x_{-u}) ∈ Ω}` is convex and `λ_u R_u(·, x_{-u})` is convex on it. -/
theorem user_problem_convex {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (u : Fin N) (x : Fin N → Tier → ℝ) :
    Convex ℝ {y ∈ Ktil P u | Function.update x u y ∈ Omega P} ∧
      ConvexOn ℝ {y ∈ Ktil P u | Function.update x u y ∈ Omega P}
        (fun y => cost P u (Function.update x u y)) := by sorry

end OffloadGNEP.Exist
