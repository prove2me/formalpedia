-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_dbl_eq
-- name    : GlobalTheory.Ex.NumD.Hom.dbl_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:50:39.52735+00:00
-- url     : https://prove2.me/theorems/ea6b10f8-1ffa-4df8-a308-826ec13bb0c4
-- title:
--   Hom: dbl eq
-- statement:
--   The Hom construction uses the dbl eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L28-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L28-L38

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

theorem GlobalTheory.Ex.NumD.Hom.dbl_eq (x : N.A) :
    dbl N'.θ N'.σ (I.φ x) * I.h (x * x) = F (dbl N.θ N.σ x) * I.h x ^ 4 := by sorry
