-- Prove2me | Theorems.Thm_GlobalTheory_SemilinearExt_extOfBasis_basis
-- name    : GlobalTheory.SemilinearExt.extOfBasis_basis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:01:38.804195+00:00
-- url     : https://prove2.me/theorems/45c45ed2-4b07-4fb2-955d-a19a6d57f907
-- title:
--   Semilinear Ext: ext Of Basis basis
-- statement:
--   The Semilinear Ext construction uses the ext Of Basis basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsBasisTensor.lean#L59-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsBasisTensor.lean#L59-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_SemilinearExtensionBases
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsBasisTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open Module
open GlobalTheory GlobalTheory.SemilinearExt
open GlobalTheory.IndefiniteRowSideFullHecke.SemilinearExtensionBases

theorem GlobalTheory.SemilinearExt.extOfBasis_basis {L L' V V' : Type} [Field L] [Field L'] [AddCommGroup V] [Module L V] [AddCommGroup V']
    [Module L' V'] (σ : L →+* L') {n : ℕ} (B : Basis (Fin n) L V) (w : Fin n → V') (k : Fin n) :
    extOfBasis σ B w (B k) = w k := by sorry
