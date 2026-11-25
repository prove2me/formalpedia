-- Prove2me | Theorems.Thm_GlobalTheory_T_affine_glue_separated
-- name    : GlobalTheory.T.affine_glue_separated
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:16:05.466437+00:00
-- url     : https://prove2.me/theorems/fdad0497-0876-418c-8a8e-c9db8de514d9
-- title:
--   T: affine glue separated
-- statement:
--   The T construction uses the affine glue separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineGlueSeparatedStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AffineGlueSeparatedStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparated
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SecEquivResM
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AffineGlueSeparatedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AffGlue
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.affine_glue_separated : ∀ {T : Scheme.{0}} (D : GlobalTheory.AffGlue.Data T) {V : T.Opens} (hV : IsAffineOpen V) {ι : Type} (W : ι → T.Opens) (hW : ∀ i, IsAffineOpen (W i)) (hWV : ∀ i, W i ≤ V), V ≤ ⨆ i, W i → ∀ x : D.M V hV, (∀ i, D.ρ hV (hW i) (hWV i) x = 0) → x = 0 := by sorry
