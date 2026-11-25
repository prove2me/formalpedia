-- Prove2me | Theorems.Thm_GlobalTheory_CountId_Cm_Yb
-- name    : GlobalTheory.CountId.Cm_Yb
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:02:36.770024+00:00
-- url     : https://prove2.me/theorems/33894b66-b229-40a9-9d71-8bed45310ded
-- title:
--   Count Id: Cm Yb
-- statement:
--   The Count Id construction uses the Cm Yb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ToMatrixTwRight.lean#L151-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ToMatrixTwRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.CountId
open GlobalTheory.JR
variable {n : ℕ} {E V : Type} [Field E] [AddCommGroup V] [Module E V]

theorem GlobalTheory.CountId.Cm_Yb (e : Basis (Fin n) E V) (T : V →ₗ[E] V) (v : V) (l : V →ₗ[E] E) :
    Cm (Yb e T v l) = Matrix.of fun i j : Fin n => l ((T ^ (i : ℕ)) (e j)) := by sorry
