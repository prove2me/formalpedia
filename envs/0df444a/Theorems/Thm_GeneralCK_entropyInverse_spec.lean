-- Prove2me | Theorems.Thm_GeneralCK_entropyInverse_spec
-- name    : GeneralCK.entropyInverse_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:51:11.793002+00:00
-- url     : https://prove2.me/theorems/43c2a73e-79af-473a-bc07-58bacc6f2611
-- title:
--   The lower entropy inverse takes values in the lower half interval
-- statement:
--   For every entropy value $h\in[0,1]$, let $u=H^{-1}_{\mathrm{lower}}(h)$ be the lower inverse of binary entropy in bits. Then $$0\le u\le\tfrac12,\qquad H(u)=h.$$ This characterizes the inverse used by the Bellman profiles and supplies its domain bounds to later analytic arguments.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/EtaMonotone.lean#L5-L12

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
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
open GeneralCK

theorem GeneralCK.entropyInverse_spec {h : ℝ} (h0 : 0 ≤ h) (h1 : h ≤ 1) :
    0 ≤ entropyInverse h ∧ entropyInverse h ≤ 1 / 2 ∧ H (entropyInverse h) = h := by sorry
