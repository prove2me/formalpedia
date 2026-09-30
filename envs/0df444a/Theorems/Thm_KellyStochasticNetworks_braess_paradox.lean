-- Prove2me | Theorems.Thm_KellyStochasticNetworks_braess_paradox
-- name    : KellyStochasticNetworks.braess_paradox
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:58:40.465865+00:00
-- url     : https://prove2.me/theorems/4c043788-0e4f-4cc1-b21d-3eaf80ebf816
-- title:
--   Braess's paradox: adding a road raises the equilibrium delay from 83 to 92
-- statement:
--   Cars travel from south to north through the network of Figure 4.3, at a total rate of six per
--   unit time. There are four one-way roads: $S\to W$ and $E\to N$, each with delay $10y$ when
--   carrying flow $y$, and $W\to N$ and $S\to E$, each with delay $y+50$. Two routes are available,
--   $S\to W\to N$ and $S\to E\to N$.
--
--   1. **Before.** Splitting the traffic evenly, three cars per unit time on each route, is a
--      Wardrop equilibrium, and every route has total delay
--      $$10\cdot 3 + (3+50) = 83 .$$
--
--   2. **After.** Add one more road, $W\to E$, with delay $y+10$. A third route $S\to W\to E\to N$
--      becomes available. Splitting the traffic evenly three ways, two cars per unit time on each
--      route, is a Wardrop equilibrium of the enlarged network, and every route now has total
--      delay
--      $$10\cdot 4 + (2+50) = (2+50) + 10\cdot 4 = 10\cdot 4 + (2+10) + 10\cdot 4 = 92 .$$
--
--   Adding road capacity raised every driver's delay, from $83$ to $92$. This is **Braess's
--   paradox**. It is not a failure of the equilibrium concept: in both networks no individual
--   driver can improve by switching, which is precisely the point. It is a failure of the selfish
--   objective to coincide with the social one, and it is in sharp contrast to an electrical
--   network, where adding a link can only make the network easier to traverse.
--
--   **Formalization Note** The two networks are given as explicit incidence matrices and explicit
--   delay functions, so the statement is a concrete arithmetic claim about named data rather than
--   a claim about a class of networks. In the second network the link flows are $4, 2, 2, 4, 2$
--   rather than all equal, which is why the delay rises: the two $10y$ roads each carry four cars
--   instead of three.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, pp. 92-94 (PDF pp. 100-102), section 4.2.1 and Figures 4.3, 4.4a, 4.4b: 'Let us fix the total flow from S to N at six cars per unit time. Figure 4.4a shows how the cars will distribute themselves. Note that all routes from S to N have the same total delay of 83 time units, so no driver has an incentive to switch route. In Figure 4.4b, we have introduced an extra road with its own delay function, and found the new distribution of traffic such that no driver has an incentive to switch route. Note that all routes again have the same total delay, but it is now 92 time units! That is, adding extra road capacity has increased everyone's delay.' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop

namespace KellyStochasticNetworks

theorem braess_paradox :
    (IsWardropEquilibrium braessIncidenceA (fun _ => (0 : Fin 1)) braessDelayA
        (fun _ => 6) ![3, 3]
      ∧ ∀ r : Fin 2, (∑ j, braessDelayA j (linkFlow braessIncidenceA ![3, 3] j)
            * braessIncidenceA j r) = 83)
  ∧ (IsWardropEquilibrium braessIncidenceB (fun _ => (0 : Fin 1)) braessDelayB
        (fun _ => 6) ![2, 2, 2]
      ∧ ∀ r : Fin 3, (∑ j, braessDelayB j (linkFlow braessIncidenceB ![2, 2, 2] j)
            * braessIncidenceB j r) = 92) := by sorry

end KellyStochasticNetworks
