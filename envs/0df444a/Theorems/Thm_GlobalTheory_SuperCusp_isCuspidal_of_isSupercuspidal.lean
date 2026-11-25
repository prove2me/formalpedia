-- Prove2me | Theorems.Thm_GlobalTheory_SuperCusp_isCuspidal_of_isSupercuspidal
-- name    : GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:40.538937+00:00
-- url     : https://prove2.me/theorems/24112cf1-8e20-5e8a-90b8-ffd90322de47
-- title:
--   Super Cusp: is Cuspidal of is Supercuspidal
-- statement:
--   The Super Cusp construction uses the is Cuspidal of is Supercuspidal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L213-L248
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsCuspidalOfIsSupercuspidal.lean#L213-L248

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CentralExponentBoundOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SubsingletonJacquetOfPerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsInvariantForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsCuspidalOfIsSupercuspidal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix Topology Filter
noncomputable section
open GlobalTheory GlobalTheory.SuperCusp

theorem GlobalTheory.SuperCusp.isCuspidal_of_isSupercuspidal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V), GlobalTheory.PRep.IsSupercuspidal π → GlobalTheory.SmGL.IsCuspidal π := by sorry
