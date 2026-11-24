-- Prove2me | Theorems.Thm_GlobalTheory_T_doubleCoset_relIndex_inf_conj_const
-- name    : GlobalTheory.T.doubleCoset_relIndex_inf_conj_const
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:32:29.699653+00:00
-- url     : https://prove2.me/theorems/e22f1695-e9b7-4541-9b9a-8af6b8c66453
-- title:
--   T: double Coset rel Index inf conj const
-- statement:
--   The T construction uses the double Coset rel Index inf conj const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConstStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/DoubleCosetRelIndexInfConjConstStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConst
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DoubleCosetRelIndexInfConjConstStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.doubleCoset_relIndex_inf_conj_const : ∀ (G : Type) [Group G] (T C K : Subgroup G), (∀ q : G, T ⊓ K.map (MulAut.conj q).toMonoidHom ≤ C) → ∀ t ∈ T, ∀ k ∈ K, ∀ q : G, (T ⊓ K.map (MulAut.conj (t * q * k)).toMonoidHom).relIndex C = (T ⊓ K.map (MulAut.conj q).toMonoidHom).relIndex C := by sorry
