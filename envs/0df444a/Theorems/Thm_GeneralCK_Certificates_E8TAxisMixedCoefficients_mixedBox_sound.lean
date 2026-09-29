-- Prove2me | Theorems.Thm_GeneralCK_Certificates_E8TAxisMixedCoefficients_mixedBox_sound
-- name    : GeneralCK.Certificates.E8TAxisMixedCoefficients.mixedBox_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-25T00:15:28.492463+00:00
-- url     : https://prove2.me/theorems/694d46b1-ddeb-4b14-95d3-ce753ebedffd
-- title:
--   Interval soundness of the E8 mixed-derivative polynomials
-- statement:
--   Suppose four order-five interval jets enclose the six components of a real jet $q$ at $t,2s+t,s+t,s$, respectively. For every pair of natural indices $(i,j)$, the interval polynomial mixedBox encloses the corresponding scalar polynomial mixed$(q,s,t,i,j)$. The source defines all index cases explicitly, including its zero default.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/E8TAxisMixedCoefficients.lean#L513-L567

import Definitions.Def_GeneralCK_E8_canonical_inverse_jet
import Definitions.Def_GeneralCK_E8_interval_checkers
import Definitions.Def_GeneralCK_E8_mixed_polynomial_interface
import Definitions.Def_GeneralCK_E8_semantic_core
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Data.Int.DivMod
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.E8TAxisMixedCoefficients
open DyadicInterval
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

theorem GeneralCK.Certificates.E8TAxisMixedCoefficients.mixedBox_sound {p : ℕ} {a b c d : DyadicJet5Enclosure p}
    {q : Jet5} {s t : ℝ}
    (ha : a.Contains q t) (hb : b.Contains q (2 * s + t))
    (hc : c.Contains q (s + t)) (hd : d.Contains q s) (i j : ℕ) :
    (mixedBox a b c d i j).Contains (mixed q s t i j) := by sorry
