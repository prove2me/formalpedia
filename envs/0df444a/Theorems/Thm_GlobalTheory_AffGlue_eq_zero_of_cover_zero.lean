-- Prove2me | Theorems.Thm_GlobalTheory_AffGlue_eq_zero_of_cover_zero
-- name    : GlobalTheory.AffGlue.eq_zero_of_cover_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:03:18.59489+00:00
-- url     : https://prove2.me/theorems/bd714416-73be-4085-9f5d-19ed79cc8107
-- title:
--   Aff Glue: eq zero of cover zero
-- statement:
--   The Aff Glue construction uses the eq zero of cover zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineGlueSeparated.lean#L9-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineGlueSeparated.lean#L9-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option autoImplicit false
open GlobalTheory GlobalTheory.AffGlue

theorem GlobalTheory.AffGlue.eq_zero_of_cover_zero : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by sorry
