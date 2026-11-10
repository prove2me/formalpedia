-- Prove2me | Theorems.Thm_MultitaskContracts_observation_3
-- name    : MultitaskContracts.observation_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:15.274252+00:00
-- url     : https://prove2.me/theorems/76017059-ad9d-422b-b47e-ee46a7dfefd4
-- title:
--   Observation 3 — independent tasks satisfy MMLRP, and hence (3)
-- statement:
--   Let $I$ be an instance of the multitask model whose tasks are independent, i.e. $P_S(Y)=\prod_{k\in Y\cap S}p_k\prod_{k\in Y\setminus S}q_k\prod_{k\in S\setminus Y}(1-p_k)\prod_{k\notin S\cup Y}(1-q_k)$. Then $I$ satisfies MMLRP,
--   $$P_{S'}(Y')\,P_S(Y)\ \ge\ P_{S'}(Y)\,P_S(Y')\qquad(S\subseteq S',\ Y\subseteq Y'),$$
--   and success on all tasks is the strongest indicator of full effort, $P_K(K)P_S(Y)\ge P_K(Y)P_S(K)$ for all $S,Y$.
--
--   This is the inclusion Independent $\subset$ MMLRP $\subset$ Strongest indicator; it makes every result proved under (3) available for independent tasks.
--
--   Differences from the source: none.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Observation 3, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_IsIndependent
import Definitions.Def_MultitaskContracts_Instance_MMLRP
import Definitions.Def_MultitaskContracts_Instance_StrongestIndicator

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Observation 3** (p.43, PDF 45). Independent tasks satisfy MMLRP, and hence eq. (3).
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Observation 3, p.43. -/
theorem observation_3 (I : Instance K) (h : I.IsIndependent) :
    I.MMLRP ∧ I.StrongestIndicator := by sorry

end MultitaskContracts
