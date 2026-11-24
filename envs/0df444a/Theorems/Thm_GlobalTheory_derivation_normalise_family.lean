-- Prove2me | Theorems.Thm_GlobalTheory_derivation_normalise_family
-- name    : GlobalTheory.derivation_normalise_family
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:10.023221+00:00
-- url     : https://prove2.me/theorems/ba2d35ae-a608-43fa-956c-1b7c7c60d89b
-- title:
--   Global Theory: derivation normalise family
-- statement:
--   The Global Theory construction uses the derivation normalise family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationsDualToFamilyOfNilpotentAug.lean#L4-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsDerivationsDualToFamilyOfNilpotentAug.lean#L4-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsDerivationsDualToFamilyOfNilpotentAug
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct

theorem GlobalTheory.derivation_normalise_family : ∀ (k A : Type) [Field k] [CommRing A] [Algebra k A] (ε : A →ₐ[k] k), IsNilpotent (RingHom.ker ε) → ∀ (d : ℕ) (x : Fin d → A) (D : Fin d → Derivation k A A), (∀ i j, ε (D i (x j)) = if i = j then 1 else 0) → ∃ E : Fin d → Derivation k A A, ∀ i j, E i (x j) = if i = j then 1 else 0 := by sorry
