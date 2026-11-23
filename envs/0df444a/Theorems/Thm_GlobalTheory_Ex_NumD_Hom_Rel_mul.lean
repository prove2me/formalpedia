-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_Rel_mul
-- name    : GlobalTheory.Ex.NumD.Hom.Rel.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:14.803298+00:00
-- url     : https://prove2.me/theorems/926a603b-763c-48ba-9ed8-be6189c35df1
-- title:
--   Rel: mul
-- statement:
--   The Rel construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L86-L97

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
variable {I}

theorem GlobalTheory.Ex.NumD.Hom.Rel.mul {g h : N.Gt} {g' h' : N'.Gt} (hg : I.Rel g g') (hh : I.Rel h h') : I.Rel (g * h) (g' * h') := by sorry
