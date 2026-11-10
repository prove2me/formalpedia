-- Prove2me | Theorems.Thm_MultitaskContracts_observation_2
-- name    : MultitaskContracts.observation_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:34:16.49689+00:00
-- url     : https://prove2.me/theorems/2a8108ca-521a-482a-9ccc-4f68261f82d2
-- title:
--   Observation 2 — MMLRP implies the strongest-indicator condition (3)
-- statement:
--   Let $I$ be an instance of the multitask model on a finite task set $K$, with distributions $P_S$ over performances. If $P$ satisfies the Multivariate Monotone Likelihood Ratio Property, i.e. $P_{S'}(Y')P_S(Y)\ge P_{S'}(Y)P_S(Y')$ whenever $S\subseteq S'$ and $Y\subseteq Y'$, then success on all tasks is the strongest indicator of full effort:
--   $$P_K(K)\,P_S(Y)\ \ge\ P_K(Y)\,P_S(K)\qquad\text{for all } S,Y\subseteq K.$$
--
--   This is the inclusion MMLRP $\subset$ Strongest indicator of the dependence hierarchy of Section 2.
--
--   Differences from the source: none.
-- source:
--   Saig, Talgam-Cohen, Tolkowsky, Multitask Contracts: Realizing the Value of Bundling, STOC 2027 submission (held version, sha256 e991a51a…), Observation 2, p.43 (PDF p.45)

import Mathlib
import Definitions.Def_MultitaskContracts_Instance
import Definitions.Def_MultitaskContracts_Instance_MMLRP
import Definitions.Def_MultitaskContracts_Instance_StrongestIndicator

set_option autoImplicit false

namespace MultitaskContracts

open scoped ENNReal

variable {K : Type*} [Fintype K] [DecidableEq K]

/-- **Observation 2** (p.43, PDF 45). If `P` satisfies MMLRP, then it satisfies eq. (3).
E. Saig, I. Talgam-Cohen, Y. Tolkowsky, *Multitask Contracts: Realizing the Value of Bundling*,
STOC 2027 submission (held version, sha256 e991a51a…), Observation 2, p.43. -/
theorem observation_2 (I : Instance K) (h : I.MMLRP) : I.StrongestIndicator := by sorry

end MultitaskContracts
