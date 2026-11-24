-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_adjoin_rootOfUnity_eq_integers
-- name    : GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:37:26.37804+00:00
-- url     : https://prove2.me/theorems/97ce8459-dc11-4865-bf92-4c62ce52d1dd
-- title:
--   Unr: adjoin root Of Unity eq integers
-- statement:
--   The Unr construction uses the adjoin root Of Unity eq integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic.lean#L69-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic.lean#L69-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinPrimitiveRootEqIntegersUnramifiedQuadratic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial IsLocalRing

theorem GlobalTheory.UnitLemma.Unr.adjoin_rootOfUnity_eq_integers : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), IsUnrExt K K' d φ → d ≠ 0 → ∀ z : K'.E, IsPrimitiveRoot z (K'.q ^ 2 - 1) → @Algebra.adjoin K.E K'.E _ _ φ.toAlgebra {z} = ⊤ → ∀ y : K'.E, @IsIntegral K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra y → y ∈ @Algebra.adjoin K.O K'.E _ _ (φ.comp (algebraMap K.O K.E)).toAlgebra {z} := by sorry
