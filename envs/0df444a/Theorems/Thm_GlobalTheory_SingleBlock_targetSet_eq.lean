-- Prove2me | Theorems.Thm_GlobalTheory_SingleBlock_targetSet_eq
-- name    : GlobalTheory.SingleBlock.targetSet_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:07.283809+00:00
-- url     : https://prove2.me/theorems/a3b6483e-608d-4f92-80ba-3a38ca77334e
-- title:
--   Single Block: target Set eq
-- statement:
--   The Single Block construction uses the target Set eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L181-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/T2SpaceIsNonarchimedeanLocalFieldSingleBlock.lean#L181-L210

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

theorem GlobalTheory.SingleBlock.targetSet_eq (hϖ : Irreducible ϖ) {P : Subgroup (GL (Fin r) F)} (hP : P ≤ GLint 𝒪[F] r) :
    targetSet t 𝒪[F] (ϖ : F) P =
      (((blockPar t (residueImage P)).comap
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (IsLocalRing.residue 𝒪[F]))).map
        (GeneralLinearGroup.map (n := Fin r ⊕ Fin t) (𝒪[F]).subtype) :
          Subgroup (GL (Fin r ⊕ Fin t) F)) := by sorry
