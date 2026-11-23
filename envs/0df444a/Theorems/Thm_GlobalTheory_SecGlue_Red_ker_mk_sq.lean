-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_ker_mk_sq
-- name    : GlobalTheory.SecGlue.Red.ker_mk_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:03.776901+00:00
-- url     : https://prove2.me/theorems/5d4bac0c-a17a-482e-a32a-cf6a8b799c50
-- title:
--   Red: ker mk sq
-- statement:
--   The Red construction uses the ker mk sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L42-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AwayMapEqOfRed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.Red
variable {R R₀ : Type} [CommRing R] [CommRing R₀]

theorem GlobalTheory.SecGlue.Red.ker_mk_sq (π : R →+* R₀) (h : RingHom.ker π ^ 2 = ⊥) (S : Type) [CommRing S]
    [Algebra R S] : RingHom.ker (Ideal.Quotient.mk (redI π S)) ^ 2 = ⊥ := by sorry
