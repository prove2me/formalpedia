-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_IsRed_eq
-- name    : GlobalTheory.SecGlue.Red.IsRed.eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:18:06.799804+00:00
-- url     : https://prove2.me/theorems/dc62a4f8-963c-4e24-8a05-a36797195db4
-- title:
--   Is Red: eq
-- statement:
--   The Is Red construction uses the eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L50-L54

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

theorem GlobalTheory.SecGlue.Red.IsRed.eq {π : R →+* R₀} {hπ : Function.Surjective π} {Y : Scheme.{0}} {g₀ : Sp R₀ ⟶ Y}
    {S : Type} [CommRing S] [Algebra R S] {u v : Sp S ⟶ Y} (hu : IsRed π hπ g₀ S u)
    (hv : IsRed π hπ g₀ S v) :
    spMap (Ideal.Quotient.mk (redI π S)) ≫ u = spMap (Ideal.Quotient.mk (redI π S)) ≫ v := by sorry
