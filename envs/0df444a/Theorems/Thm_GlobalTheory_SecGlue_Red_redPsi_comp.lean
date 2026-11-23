-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_redPsi_comp
-- name    : GlobalTheory.SecGlue.Red.redPsi_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:30:30.233728+00:00
-- url     : https://prove2.me/theorems/bae11472-fc77-4909-bd61-1bff8989b91c
-- title:
--   Red: red Psi comp
-- statement:
--   The Red construction uses the red Psi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L38-L40

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

theorem GlobalTheory.SecGlue.Red.redPsi_comp (π : R →+* R₀) (hπ : Function.Surjective π) (S : Type) [CommRing S]
    [Algebra R S] : (redPsi π hπ S).comp π = (Ideal.Quotient.mk (redI π S)).comp (algebraMap R S) := by sorry
