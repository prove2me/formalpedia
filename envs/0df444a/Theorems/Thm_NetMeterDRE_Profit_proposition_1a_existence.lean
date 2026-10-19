-- Prove2me | Theorems.Thm_NetMeterDRE_Profit_proposition_1a_existence
-- name    : NetMeterDRE.Profit.proposition_1a_existence
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T22:19:37.84184+00:00
-- url     : https://prove2.me/theorems/e297b283-da78-4f26-ab3a-874df23c788a
-- title:
--   Proposition 1(a), p. 12 (PDF 12), existence half — the symmetric supply S(p) = (N−2)p/((N−1)2c) is a supply function equilibrium
-- statement:
--   Consider the wholesale market with $N > 2$ generators, each with production cost $c q^2$ for a constant $c > 0$. Let every generator submit the same supply function
--   $$S(p) = \frac{(N-2)\,p}{(N-1)\,2c}.$$
--   Then the symmetric profile $(S, S, \dots, S)$ is a supply function equilibrium in the sense of Definition 1: for every generator, every realization of the net wholesale demand, every alternative supply function and every price that clears the market after the deviation, the deviating generator's profit does not exceed its profit in the symmetric profile.
--
--   This is the existence half of Proposition 1(a) of Sunar and Swaminathan, the equilibrium their proof of Proposition 1 exhibits; all later results of the paper are stated in this equilibrium.
--
--   **Formalization Note** Only existence is stated. The uniqueness half of Proposition 1(a) (uniqueness among symmetric supply function equilibria) is not part of this item.
-- source:
--   Sunar & Swaminathan, Net-metered distributed renewable energy: A peril for utilities?, SSRN 3257925 (version of September 2019), p. 12 (PDF 12), Proposition 1(a); proof on pp. ec3–ec4 (PDF 35–36)

import Mathlib
import Definitions.Def_NetMeterDRE_Profit_SFE

namespace NetMeterDRE.Profit

theorem proposition_1a_existence (N : ℕ) (c : ℝ) (hN : 2 < N) (hc : 0 < c) :
    IsSFE N c (fun _ : Fin N => symSupply N c) := by sorry

end NetMeterDRE.Profit
