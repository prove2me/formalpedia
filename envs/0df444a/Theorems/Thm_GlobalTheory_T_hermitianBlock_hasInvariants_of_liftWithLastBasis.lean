-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianBlock_hasInvariants_of_liftWithLastBasis
-- name    : GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:19.344807+00:00
-- url     : https://prove2.me/theorems/dcbc022f-d786-576c-b8e6-48ff2feffae4
-- title:
--   T: hermitian Block has Invariants of lift With Last Basis
-- statement:
--   The T construction uses the hermitian Block has Invariants of lift With Last Basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasisStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/HermitianBlockHasInvariantsOfLiftWithLastBasisStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FullToGlIsSelfAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_HermitianBlockHasInvariantsOfLiftWithLastBasisStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitianBlock_hasInvariants_of_liftWithLastBasis : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ) (Z : Gl r F) (X : Hn r F E) (μ l : F) (ν : E), ν * star ν = algebraMap F E μ → μ ≠ 0 → Delta (inv (GlobalTheory.JR.Step.lift Z μ l)) ≠ 0 → Delta (inv Z) ≠ 0 → HasInv X (inv Z) → HasInv (GlobalTheory.JR.Step.liftH X ν l) (inv (GlobalTheory.JR.Step.lift Z μ l)) := by sorry
