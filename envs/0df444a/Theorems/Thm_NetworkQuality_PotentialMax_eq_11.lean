-- Prove2me | Theorems.Thm_NetworkQuality_PotentialMax_eq_11
-- name    : NetworkQuality.PotentialMax.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:43:00.401749+00:00
-- url     : https://prove2.me/theorems/2ed276d2-5bfe-4e50-962d-ec521ec63cf8
-- title:
--   (11), p. 13 — the stage-2 subgame is a weighted potential game with potential Φ and weights v_i
-- statement:
--   In the network market with valuations $v_i>0$, benefit $f$ and potential $\Phi(B,p,q)=\sum_{i=1}^{|B|}f(i,q)-p\sum_{i\in B}1/v_i$, for every consumer $i\in N$, every set $B_{-i}\subseteq N\setminus\{i\}$ of other buyers, every price $p$ and every quality $q$,
--   $$u_i(B_{-i}\cup\{i\},p,q)-u_i(B_{-i},p,q)=v_i\big[\Phi(B_{-i}\cup\{i\},p,q)-\Phi(B_{-i},p,q)\big].$$
--
--   Every unilateral deviation changes the deviator's payoff by $v_i$ times the change in $\Phi$, so the stage-2 subgame is a weighted potential game with weights $v_i$. This is what makes potential maximization available as an equilibrium-selection criterion.
--
--   **Formalization Note** The identity uses $v_i\neq 0$, which the standing assumptions ($v_i>0$) supply; they are taken as a hypothesis for uniformity with the other statements.
-- source:
--   Chan, Quality Strategies in Network Markets, SSRN 4203818 (version of April 2023), p. 13, (11)

import Mathlib
import Definitions.Def_NetworkQuality_PotentialMax_Setting

namespace NetworkQuality.PotentialMax

open Market

theorem eq_11 {n : ℕ} (M : Market n) (hM : M.Standing) (i : Fin n) (B : Finset (Fin n))
    (hi : i ∉ B) (p q : ℝ) :
    M.u i (insert i B) p q - M.u i B p q =
      M.v i * (M.pot (insert i B) p q - M.pot B p q) := by sorry

end NetworkQuality.PotentialMax
