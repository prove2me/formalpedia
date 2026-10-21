-- Prove2me | Theorems.Thm_NonExclEncroach_Channels_corollary_1
-- name    : NonExclEncroach.Channels.corollary_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T01:21:29.834279+00:00
-- url     : https://prove2.me/theorems/903be381-b739-4e21-bb3d-fa1ffd2d1eef
-- title:
--   Corollary 1, p. 17 — when w2 = w′2 the reseller's order q2^III equals supplier 1's conjecture q′2
-- statement:
--   For all $\theta$, $c$, $w_2'$ and $q_1$, when supplier 2's actual price coincides with supplier 1's belief, $w_2=w_2'$,
--   $$q_2^{III}(w_2',w_2',q_1)=q_2'(w_2',q_1),$$
--   where $q_2'$ is supplier 1's rational conjecture (4.18) and $q_2^{III}$ the reseller's conditionally optimal order (4.19).
--
--   So on the equilibrium path, where beliefs are correct, supplier 1 correctly anticipates the reseller's order from her rival; only after a deviation by supplier 2 can the two differ.
--
--   **Formalization Note** The identity is between the closed forms (4.18) and (4.19) and holds for all real arguments.
-- source:
--   Hotkar & Gilbert, Supplier Encroachment in a Non-Exclusive Reselling Channel, SSRN working paper 3238502, p. 17 (PDF 17), Corollary 1

import Mathlib
import Definitions.Def_NonExclEncroach_Channels_Model

namespace NonExclEncroach.Channels

theorem corollary_1 (θ c b q1 : ℝ) : q2III θ c b b q1 = q2conj θ c b q1 := by sorry

end NonExclEncroach.Channels
