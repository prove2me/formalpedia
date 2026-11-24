-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_Red_isRed_comp
-- name    : GlobalTheory.SecGlue.Red.isRed_comp
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:49:02.825779+00:00
-- url     : https://prove2.me/theorems/a9ac90cc-3802-4e80-8e48-3eb60319e371
-- title:
--   Red: is Red comp
-- statement:
--   The Red construction uses the is Red comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L85-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AwayMapEqOfRed.lean#L85-L104

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

theorem GlobalTheory.SecGlue.Red.isRed_comp (π : R →+* R₀) (hπ : Function.Surjective π) {Y : Scheme.{0}}
    (g₀ : Sp R₀ ⟶ Y) {S S' : Type} [CommRing S] [Algebra R S] [CommRing S'] [Algebra R S']
    (σ : S →+* S') (hσ : σ.comp (algebraMap R S) = algebraMap R S') {u : Sp S ⟶ Y}
    (hu : IsRed π hπ g₀ S u) : IsRed π hπ g₀ S' (spMap σ ≫ u) := by sorry
