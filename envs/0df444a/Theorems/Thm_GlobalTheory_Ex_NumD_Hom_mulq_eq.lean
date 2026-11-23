-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_mulq_eq
-- name    : GlobalTheory.Ex.NumD.Hom.mulq_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:06.167128+00:00
-- url     : https://prove2.me/theorems/6aedc810-92e6-44ba-a5bb-a2f29e19fde9
-- title:
--   Hom: mulq eq
-- statement:
--   The Hom construction uses the mulq eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L40-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L40-L54

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

theorem GlobalTheory.Ex.NumD.Hom.mulq_eq (n : ℕ) (x : N.A) :
    mulq N'.θ N'.σ n (I.φ x) * I.h x ^ (n ^ 2) = F (mulq N.θ N.σ n x) * I.h (x ^ n) := by sorry
