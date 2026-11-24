-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_evT_eq
-- name    : GlobalTheory.Ex.NumD.Hom.evT_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:06:42.804775+00:00
-- url     : https://prove2.me/theorems/071236f3-399a-4a75-813a-e9fbebb924b5
-- title:
--   Hom: ev T eq
-- statement:
--   The Hom construction uses the ev T eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L204-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L204-L224

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

theorem GlobalTheory.Ex.NumD.Hom.evT_eq {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (χ : N.X) (h : N.Gt) (h' : N'.Gt) (hh : I.Rel h h') :
    N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) := by sorry
