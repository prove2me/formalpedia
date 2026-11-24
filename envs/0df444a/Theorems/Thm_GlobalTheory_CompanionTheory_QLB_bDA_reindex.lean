-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLB_bDA_reindex
-- name    : GlobalTheory.CompanionTheory.QLB.bDA_reindex
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T14:35:35.655682+00:00
-- url     : https://prove2.me/theorems/56245acc-7b2a-4097-b933-b131b64b4b49
-- title:
--   QLB: b DA reindex
-- statement:
--   The QLB construction uses the b DA reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L27-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L27-L28

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
variable {r d c : ℕ} (A : Matrix (Fin r) (Fin r) F) (B : Matrix (Fin r) (Fin c) F)
  (C : Matrix (Fin d) (Fin r) F) (D : Matrix (Fin d) (Fin c) F)

theorem GlobalTheory.CompanionTheory.QLB.bDA_reindex : bDA (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A B C D)) = C := by sorry
