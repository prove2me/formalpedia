-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_isGNEPSol_of_isVISol
-- name    : OffloadGNEP.Exist.isGNEPSol_of_isVISol
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:55.076822+00:00
-- url     : https://prove2.me/theorems/52665937-89bc-4c24-8ebe-d5511da293be
-- title:
--   Proof of Proposition 1, p. 12 — under Assumption A every solution of VI(K, F) solves the GNEP (10)–(15)
-- statement:
--   Assume Assumption A and the standing hypotheses. If $\bar x\in K$ satisfies
--   $$F(\bar x)^\top(x-\bar x)\ge0\qquad\text{for all }x\in K,$$
--   then $\bar x$ is a solution of the GNEP (10)–(15): for every user $u$, $\bar x_u$ minimises $\lambda_uR_u(\cdot,\bar x_{-u})$ over $\{y\in\tilde K_u:(y,\bar x_{-u})\in\Omega\}$.
--
--   This is the reduction of a jointly convex GNEP to a single variational inequality (the paper cites Facchinei, Fischer and Piccialli [15]); the equilibria obtained this way are the variational, or normalized, solutions.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, proof of Proposition 1 (citing [15])

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- Proof of Proposition 1, p. 12 (citing [15]): under Assumption A any solution of the VI(K, F)
(a variational solution) is a solution of the GNEP (10)–(15). -/
theorem isGNEPSol_of_isVISol {N : ℕ} (P : Params N) (hA : P.AssumptionA) (hS : P.Standing)
    (xb : Fin N → Tier → ℝ) (h : IsVISol (K P) (F P) xb) : IsGNEPSol P xb := by sorry

end OffloadGNEP.Exist
