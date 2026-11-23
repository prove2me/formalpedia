-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_wQ_eq
-- name    : GlobalTheory.Ex.NumD.Hom.wQ_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:48.844916+00:00
-- url     : https://prove2.me/theorems/1f13d96f-1282-4a0d-9890-55657cc04e22
-- title:
--   Hom: w Q eq
-- statement:
--   The Hom construction uses the w Q eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L153-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L153-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)

theorem GlobalTheory.Ex.NumD.Hom.wQ_eq {k : ℕ} (hk : Odd k) (p : N.QT k) (p' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) : N'.wQ p' * I.h p.1.2.b ^ k = F (N.wQ p) := by sorry
