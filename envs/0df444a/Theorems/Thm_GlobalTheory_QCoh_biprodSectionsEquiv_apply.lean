-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_biprodSectionsEquiv_apply
-- name    : GlobalTheory.QCoh.biprodSectionsEquiv_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T06:09:04.314238+00:00
-- url     : https://prove2.me/theorems/f65b9b52-374b-4602-9e14-1aeb6de0f58e
-- title:
--   QCoh: biprod Sections Equiv apply
-- statement:
--   The QCoh construction uses the biprod Sections Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L618-L620
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L618-L620

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsQuasicoherentOfForallExistsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExactAndSurjectiveAppOfExactOfEpi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
universe w' w u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {M N P : X.Modules} {U V : X.Opens}

theorem GlobalTheory.QCoh.biprodSectionsEquiv_apply (M N : X.Modules) (U : X.Opens) (s : Γ(M ⊞ N, U)) :
    biprodSectionsEquiv M N U s =
      ((biprod.fst : M ⊞ N ⟶ M).app U s, (biprod.snd : M ⊞ N ⟶ N).app U s) := by sorry

attribute [defeq] GlobalTheory.QCoh.biprodSectionsEquiv_apply
