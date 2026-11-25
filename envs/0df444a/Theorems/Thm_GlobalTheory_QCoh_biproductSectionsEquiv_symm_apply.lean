-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_biproductSectionsEquiv_symm_apply
-- name    : GlobalTheory.QCoh.biproductSectionsEquiv_symm_apply
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:18:11.225324+00:00
-- url     : https://prove2.me/theorems/9e909d60-a0b3-5760-95f7-7fa838ace7fb
-- title:
--   QCoh: biproduct Sections Equiv symm apply
-- statement:
--   The QCoh construction uses the biproduct Sections Equiv symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L596-L598
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L596-L598

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

theorem GlobalTheory.QCoh.biproductSectionsEquiv_symm_apply {ι : Type} [Fintype ι] (F : ι → X.Modules)
    [HasBiproduct F] (U : X.Opens) (s : ∀ i, Γ(F i, U)) :
    (biproductSectionsEquiv F U).symm s = ∑ i, (biproduct.ι F i).app U (s i) := by sorry
