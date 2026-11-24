-- Prove2me | Theorems.Thm_GlobalTheory_PeriodConn_isPeriod_mulVec
-- name    : GlobalTheory.PeriodConn.isPeriod_mulVec
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:39.23221+00:00
-- url     : https://prove2.me/theorems/3d7abfb3-f432-45a3-83a3-67a02ece8739
-- title:
--   Period Conn: is Period mul Vec
-- statement:
--   The Period Conn construction uses the is Period mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsPreconnectedBlockUnits.lean#L24-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/IsPreconnectedBlockUnits.lean#L24-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsPreconnectedBlockUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Matrix
open GlobalTheory GlobalTheory.PeriodConn
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
open NumberField Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem GlobalTheory.PeriodConn.isPeriod_mulVec {D : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H} {g : ℕ}
    {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)}
    (hP : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty P) {A : Matrix (Fin g) (Fin g) ℂ} (hA : A.det ≠ 0)
    (hty : ∀ i j, ty i ≠ ty j → A i j = 0) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsPeriod D ty ((A.mulVecLin).toAddMonoidHom.comp P) := by sorry
