-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_defect_swap
-- name    : GlobalTheory.InducedPBW.defect_swap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:35.364802+00:00
-- url     : https://prove2.me/theorems/e41c9b39-ea52-4f32-ac95-d926c13605c1
-- title:
--   Induced PBW: defect swap
-- statement:
--   The Induced PBW construction uses the defect swap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L310-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L310-L313

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
variable (hf : step e c act δ = δ)
include hf
omit hce hf [LinearOrder ι]

theorem GlobalTheory.InducedPBW.defect_swap (m : MvPolynomial ι R ⊗[R] V) (x y : g) :
    defect c δ m x y = - defect c δ m y x := by sorry
