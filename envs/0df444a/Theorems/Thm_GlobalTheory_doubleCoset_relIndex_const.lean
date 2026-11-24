-- Prove2me | Theorems.Thm_GlobalTheory_doubleCoset_relIndex_const
-- name    : GlobalTheory.doubleCoset_relIndex_const
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:16:36.732255+00:00
-- url     : https://prove2.me/theorems/dc478347-2d15-450b-a719-9fcaff64788e
-- title:
--   Global Theory: double Coset rel Index const
-- statement:
--   The Global Theory construction uses the double Coset rel Index const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L63-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConst.lean#L63-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

theorem GlobalTheory.doubleCoset_relIndex_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by sorry
