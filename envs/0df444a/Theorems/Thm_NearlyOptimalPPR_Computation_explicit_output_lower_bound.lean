-- Prove2me | Theorems.Thm_NearlyOptimalPPR_Computation_explicit_output_lower_bound
-- name    : NearlyOptimalPPR.Computation.explicit_output_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:15:50.638529+00:00
-- url     : https://prove2.me/theorems/7d6929a6-fb6b-4d4e-8015-6fbdcc1a2e1c
-- title:
--   Explicit-output lower bound from center-seeded stars
-- statement:
--   Fix $0<\alpha<1$ and set $\beta=(1-\alpha)/(2-\alpha)$. For every $0<\varepsilon\le\beta/4$, let $L=\lfloor\beta/(2\varepsilon)\rfloor$. The center-seeded star with $L$ leaves has
--
--   $$
--   \pi_s(s)=\frac1{2-\alpha},\qquad \pi_s(v)=\frac\beta L\quad(v\ne s),\qquad L\ge\frac\beta{4\varepsilon}\ge1.
--   $$
--
--   Every explicit sparse output satisfying the absolute coordinatewise ACL guarantee has estimate at least $\varepsilon$ at each leaf and has at least
--
--   $$
--   \frac\beta{4\varepsilon}
--   $$
--
--   entries. Labels may repeat and values may be negative: omitted labels have value zero and repeated labels are summed. This gives the explicit-output lower-bound branch of the mission's main theorem.
-- source:
--   Li, Xu, Yang, Zhou, Nearly optimal Personalized PageRank computation, STOC 2027 submission #884, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/884.pdf, p.2 explicit-output paragraph following Definition 1.1; quantitative star family spelled out in the captain-attested main theorem.

import Definitions.Def_NearlyOptimalPPR_Computation_machine
set_option autoImplicit false

namespace NearlyOptimalPPR.Computation

theorem explicit_output_lower_bound : explicitOutputLowerBound := by sorry

end NearlyOptimalPPR.Computation
