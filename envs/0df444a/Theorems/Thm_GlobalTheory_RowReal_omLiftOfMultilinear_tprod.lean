-- Prove2me | Theorems.Thm_GlobalTheory_RowReal_omLiftOfMultilinear_tprod
-- name    : GlobalTheory.RowReal.omLiftOfMultilinear_tprod
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:31:48.298049+00:00
-- url     : https://prove2.me/theorems/deb70aa2-4fb7-4230-b191-6467d1d5b9d1
-- title:
--   Row Real: om Lift Of Multilinear tprod
-- statement:
--   The Row Real construction uses the om Lift Of Multilinear tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OmLiftOfMultilinearTprod.lean#L22-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OmLiftOfMultilinearTprod.lean#L22-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_MinorOrderedEntries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OmLiftOfMultilinearTprod
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.RowReal
variable {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)

theorem GlobalTheory.RowReal.omLiftOfMultilinear_tprod
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ))) (x y v φ) :
    omLiftOfMultilinear P Φ (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) =
      Φ x y v φ := by sorry
