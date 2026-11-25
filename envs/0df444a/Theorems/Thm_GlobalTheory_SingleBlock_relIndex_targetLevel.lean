-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_relIndex_targetLevel
-- name    : GlobalTheory.SingleBlock.relIndex_targetLevel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:54:36.509226+00:00
-- url     : https://prove2.me/theorems/f12a7f54-fa2c-4e64-94dc-660c3d2ad841
-- title:
--   Single Block: rel Index target Level
-- statement:
--   The Single Block construction uses the rel Index target Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L227-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L227-L234

import Mathlib
import Definitions.Def_Formalism_DoubleCosetMeasures_LatticeCoset
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_LocalIntegralGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FromBlocksMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasCompactSupportPhiU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_T2SpaceIsNonarchimedeanLocalFieldSingleBlock
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Matrix ComplexConjugate ValuativeRel Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P GlobalTheory.IndefiniteRowSideFullHecke.LocalIntegralGL
open GlobalTheory GlobalTheory.SingleBlock
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {r t : ℕ} {ϖ : 𝒪[F]}

theorem GlobalTheory.SingleBlock.relIndex_targetLevel (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)}
    (hP : P ≤ GLint 𝒪[F] r) :
    (targetLevel t 𝒪[F] (ϖ : F) P).relIndex (glInt 𝒪[F] (Fin r ⊕ Fin t)) =
      (blockPar t (residueImage P)).index := by sorry
