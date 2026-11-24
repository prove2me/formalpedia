-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_isTorsionFree_of_injective
-- name    : GlobalTheory.InjectiveAlgebraMapTorsionFree.isTorsionFree_of_injective
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:18:47.350296+00:00
-- url     : https://prove2.me/theorems/e594d527-51dd-42a0-a2e2-016feade1bbb
-- title:
--   Injective Algebra Map Torsion Free: is Torsion Free of injective
-- statement:
--   The Injective Algebra Map Torsion Free construction uses the is Torsion Free of injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L19-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]

theorem GlobalTheory.InjectiveAlgebraMapTorsionFree.isTorsionFree_of_injective {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S := by sorry
