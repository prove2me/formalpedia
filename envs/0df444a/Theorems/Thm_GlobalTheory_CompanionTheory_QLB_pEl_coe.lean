-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLB_pEl_coe
-- name    : GlobalTheory.CompanionTheory.QLB.pEl_coe
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:56:05.973331+00:00
-- url     : https://prove2.me/theorems/d41bb379-3a5e-400b-96fc-8c4d97ebc842
-- title:
--   QLB: p El coe
-- statement:
--   The QLB construction uses the p El coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L11-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/ParabolicElementBlocks.lean#L11-L14

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

theorem GlobalTheory.CompanionTheory.QLB.pEl_coe {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F)) := by sorry
