-- Prove2me | Theorems.Thm_GlobalTheory_RowReal_invFun_of_multilinear
-- name    : GlobalTheory.RowReal.invFun_of_multilinear
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:20:50.973931+00:00
-- url     : https://prove2.me/theorems/0fefe807-5602-52ea-8255-1a9510e976d5
-- title:
--   Row Real: inv Fun of multilinear
-- statement:
--   The Row Real construction uses the inv Fun of multilinear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OmLiftOfMultilinearTprod.lean#L32-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OmLiftOfMultilinearTprod.lean#L32-L52

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

theorem GlobalTheory.RowReal.invFun_of_multilinear : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] {S : Sizes} (P : ι → Entries S)
    (Φ : MultilinearMap ℂ (fun j : Fin S.m => Pol ι (S.nR j.castSucc) (S.nR j.succ))
      (MultilinearMap ℂ (fun i : Fin S.m => Pol ι (S.nC i.castSucc) (S.nC i.succ))
        (weylSub (S.nR (0 : Fin (S.m + 1))) (psiWt P) →ₗ[ℂ]
          Module.Dual ℂ (weylSub (S.nC (0 : Fin (S.m + 1))) (baseWt P)) →ₗ[ℂ] ℂ)))
    (hΦ : ∀ g x y v φ, Φ (fun j => rowFock P j g (x j)) (fun i => colFock P i g (y i)) (psiRep P g v)
      ((baseRep P).dual g φ) = Φ x y v φ), ∃ l ∈ invFun (omRep P), ∀ x y v φ,
      l (PiTensorProduct.tprod ℂ x ⊗ₜ[ℂ] (PiTensorProduct.tprod ℂ y ⊗ₜ[ℂ] (v ⊗ₜ[ℂ] φ))) = Φ x y v φ := by sorry
