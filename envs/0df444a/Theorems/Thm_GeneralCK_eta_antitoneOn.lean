-- Prove2me | Theorems.Thm_GeneralCK_eta_antitoneOn
-- name    : GeneralCK.eta_antitoneOn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:52:08.311512+00:00
-- url     : https://prove2.me/theorems/fde9d8fa-6e8a-40b4-a402-acc67783edfd
-- title:
--   The entropy production profile is decreasing
-- statement:
--   For all entropy values $a,b\in(0,1]$ with $a\le b$, the entropy-production profile satisfies $$\eta(b)\le\eta(a).$$ This order property is used both by the entropy comparison argument and by shared radial certificate bounds.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EtaMonotone.lean#L55-L64

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman

open scoped BigOperators
open GeneralCK

theorem GeneralCK.eta_antitoneOn : AntitoneOn eta (Set.Ioc 0 1) := by sorry
