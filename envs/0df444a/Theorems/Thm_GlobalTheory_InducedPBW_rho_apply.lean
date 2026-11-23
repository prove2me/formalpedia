-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
-- name    : GlobalTheory.InducedPBW.rho_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:46:59.272433+00:00
-- url     : https://prove2.me/theorems/743fa510-d3b1-4359-bac8-f717c0fa664b
-- title:
--   Induced PBW: rho apply
-- statement:
--   The Induced PBW construction uses the rho apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L110-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L110-L111

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
omit [LinearOrder ι]

theorem GlobalTheory.InducedPBW.rho_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x m) :
    rho c δ x m = mulLin c x m + δ x m := by sorry
