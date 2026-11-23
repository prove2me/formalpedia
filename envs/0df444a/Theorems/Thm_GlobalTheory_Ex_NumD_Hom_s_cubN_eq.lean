-- Prove2me | Theorems.Thm_GlobalTheory_Ex_NumD_Hom_s_cubN_eq
-- name    : GlobalTheory.Ex.NumD.Hom.s_cubN_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:48:13.562717+00:00
-- url     : https://prove2.me/theorems/2ef1178b-64bd-4c7d-bb58-1cfb86c477ac
-- title:
--   Hom: s cub N eq
-- statement:
--   The Hom construction uses the s cub N eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L127-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/HomTransport.lean#L127-L138

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

theorem GlobalTheory.Ex.NumD.Hom.s_cubN_eq {k : ℕ} (q : N.QT k) {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') :
    g'.s (I.e q.1.1.toAdd) * cubN N'.θ k 1 (I.φ q.1.2.b) (I.φ g.b) * I.h (q.1.2.b * g.b) ^ k =
      F (g.s q.1.1.toAdd * cubN N.θ k 1 q.1.2.b g.b) * I.h q.1.2.b ^ k * I.h g.b ^ k := by sorry
