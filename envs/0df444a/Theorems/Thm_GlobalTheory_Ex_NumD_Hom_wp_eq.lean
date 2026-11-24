-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_wp_eq
-- name    : GlobalTheory.Ex.NumD.Hom.wp_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:54.508584+00:00
-- url     : https://prove2.me/theorems/f22fe535-1e6b-49a1-ad6b-5e1db55090ce
-- title:
--   Hom: wp eq
-- statement:
--   The Hom construction uses the wp eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L140-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L140-L151

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

theorem GlobalTheory.Ex.NumD.Hom.wp_eq {k : ℕ} (p q : N.QT k) (p' q' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (eq : q'.1.1.toAdd = I.e q.1.1.toAdd) (hq : I.Rel q.1.2 q'.1.2) :
    N'.wp p' q' = F (N.wp p q) := by sorry
