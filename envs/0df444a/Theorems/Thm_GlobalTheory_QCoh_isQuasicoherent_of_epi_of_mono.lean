-- Prove2me | Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_epi_of_mono
-- name    : GlobalTheory.QCoh.isQuasicoherent_of_epi_of_mono
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:19:07.094659+00:00
-- url     : https://prove2.me/theorems/9a4a9fea-671c-47c4-947b-646272750144
-- title:
--   QCoh: is Quasicoherent of epi of mono
-- statement:
--   The QCoh construction uses the is Quasicoherent of epi of mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L276-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExactAndSurjectiveAppOfExactOfEpi.lean#L276-L279

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

theorem GlobalTheory.QCoh.isQuasicoherent_of_epi_of_mono {I : X.Modules} (e : M ⟶ I) (m : I ⟶ N) [Epi e] [Mono m]
    [M.IsQuasicoherent] [N.IsQuasicoherent] : I.IsQuasicoherent := by sorry
