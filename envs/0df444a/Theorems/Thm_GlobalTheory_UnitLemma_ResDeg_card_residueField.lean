-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_ResDeg_card_residueField
-- name    : GlobalTheory.UnitLemma.ResDeg.card_residueField
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T15:36:39.91287+00:00
-- url     : https://prove2.me/theorems/5702c434-d23f-4a23-94b8-1b014159bbdf
-- title:
--   Res Deg: card residue Field
-- statement:
--   The Res Deg construction uses the card residue Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardResidueFieldAdjoinUnitaryProd.lean#L82-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/CardResidueFieldAdjoinUnitaryProd.lean#L82-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardResidueFieldAdjoinUnitaryProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.ResDeg
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Orbit Polynomial IsLocalRing
variable {K : UQ}

theorem GlobalTheory.UnitLemma.ResDeg.card_residueField (B : InvAlg K) (hu : B.g * B.σ B.g = 1) (hi : IsIntegral K.O B.g)
    (hl : IsLocalRing (Algebra.adjoin K.O ({B.g} : Set B.A))) :
    ∃ d : ℕ, Odd d ∧
      Nat.card (@IsLocalRing.ResidueField (Algebra.adjoin K.O ({B.g} : Set B.A)) _ hl) = K.q ^ (2 * d) := by sorry
