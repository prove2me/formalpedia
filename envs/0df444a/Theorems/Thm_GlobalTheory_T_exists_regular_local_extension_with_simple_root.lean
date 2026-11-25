-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_regular_local_extension_with_simple_root
-- name    : GlobalTheory.T.exists_regular_local_extension_with_simple_root
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:31:06.746665+00:00
-- url     : https://prove2.me/theorems/8b89c993-fddf-44b4-8909-580016d8a5d6
-- title:
--   T: exists regular local extension with simple root
-- statement:
--   The T construction uses the exists regular local extension with simple root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRootStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsRegularLocalExtensionWithSimpleRootStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRoot
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRegularLocalExtensionWithSimpleRootStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_regular_local_extension_with_simple_root : ∀ (A Ω : Type) [CommRing A] [IsRegularLocalRing A] [Field Ω] (u : A →+* Ω) (p : Polynomial A) (α : Ω), RingHom.ker u = maximalIdeal A → IsAdicComplete (maximalIdeal A) A → p.Monic → (p.map u).eval α = 0 → (p.map u).derivative.eval α ≠ 0 → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (a : A →+* E) (v : E →+* Ω), a.Flat ∧ (maximalIdeal A).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ α ∈ v.range := by sorry
