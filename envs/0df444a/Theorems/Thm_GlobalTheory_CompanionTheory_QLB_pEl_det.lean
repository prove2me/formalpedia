-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLB_pEl_det
-- name    : GlobalTheory.CompanionTheory.QLB.pEl_det
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T14:34:56.052888+00:00
-- url     : https://prove2.me/theorems/72b7ec1a-6a46-425d-9821-1cc5ddac0138
-- title:
--   QLB: p El det
-- statement:
--   The QLB construction uses the p El det property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L35-L38

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_ParabolicElementBlocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLB
variable {F : Type} [Field F]

theorem GlobalTheory.CompanionTheory.QLB.pEl_det {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F).det =
      (m₁ : Matrix (Fin r) (Fin r) F).det * (m₂ : Matrix (Fin c) (Fin c) F).det := by sorry
