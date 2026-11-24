-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_mulLin_e
-- name    : GlobalTheory.InducedPBW.mulLin_e
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:15:53.286335+00:00
-- url     : https://prove2.me/theorems/ecdb40d8-8c25-465d-892b-fb77d72a32b8
-- title:
--   Induced PBW: mul Lin e
-- statement:
--   The Induced PBW construction uses the mul Lin e property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L257-L258
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L257-L258

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

theorem GlobalTheory.InducedPBW.mulLin_e (i : ι) (m : MvPolynomial ι R ⊗[R] V) : mulLin c (e i) m = mulX i m := by sorry
