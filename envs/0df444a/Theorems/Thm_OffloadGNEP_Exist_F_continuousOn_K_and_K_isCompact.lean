-- Prove2me | Theorems.Thm_OffloadGNEP_Exist_F_continuousOn_K_and_K_isCompact
-- name    : OffloadGNEP.Exist.F_continuousOn_K_and_K_isCompact
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:46:33.207315+00:00
-- url     : https://prove2.me/theorems/9f34befa-72ce-4726-beef-19eddf74cc97
-- title:
--   Proof of Proposition 1, p. 12 — F is continuous on K, and K is compact (and convex)
-- statement:
--   Assume Assumption A and the standing hypotheses. Then the map $F$ is continuous on $K$, and the set $K=\big(\prod_u\tilde K_u\big)\cap\Omega\subseteq\mathbb R^{3N}$ is compact and convex.
--
--   These are the hypotheses of the basic existence theorem for variational inequalities on a compact convex set.
--
--   **Formalization Note** Convexity of $K$ is added to the paper's sentence ("F is continuous on K and K is obviously compact"): footnote 2 requires the set of a VI to be closed and convex, and the existence step uses it. It is immediate from the linear constraints.
-- source:
--   Cardellini et al., A game-theoretic approach to computation offloading in mobile cloud computing, accepted manuscript (IRIS Sapienza 11573/779661; DOI 10.1007/s10107-015-0881-6), p. 12, proof of Proposition 1

import Mathlib
import Definitions.Def_OffloadGNEP_Exist_Setting

namespace OffloadGNEP.Exist

/-- Proof of Proposition 1, p. 12: `F` is continuous on `K`, and `K` is compact (and convex,
as footnote 2 requires of the set of a VI). -/
theorem F_continuousOn_K_and_K_isCompact {N : ℕ} (P : Params N) (hA : P.AssumptionA)
    (hS : P.Standing) :
    ContinuousOn (F P) (K P) ∧ IsCompact (K P) ∧ Convex ℝ (K P) := by sorry

end OffloadGNEP.Exist
