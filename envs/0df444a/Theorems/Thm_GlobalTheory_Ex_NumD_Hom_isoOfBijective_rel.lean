-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_isoOfBijective_rel
-- name    : GlobalTheory.Ex.NumD.Hom.isoOfBijective_rel
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:05:12.690661+00:00
-- url     : https://prove2.me/theorems/97b61d96-3a0b-497c-8d2d-dbd33dff6e12
-- title:
--   Hom: iso Of Bijective rel
-- statement:
--   The Hom construction uses the iso Of Bijective rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L254-L255

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

theorem GlobalTheory.Ex.NumD.Hom.isoOfBijective_rel {M M' : NumD O} (J : NumD.Hom (RingHom.id O) M M') (hJ : Function.Bijective J.φ)
    (g : M.Gt) (g' : M'.Gt) : (J.isoOfBijective hJ).Rel g g' ↔ J.Rel g g' := by sorry
