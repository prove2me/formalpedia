-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_rho_zero_of_k
-- name    : GlobalTheory.InducedPBW.rho_zero_of_k
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:35.486323+00:00
-- url     : https://prove2.me/theorems/13f448ae-ff02-48fd-ab72-44d42d1650cd
-- title:
--   Induced PBW: rho zero of k
-- statement:
--   The Induced PBW construction uses the rho zero of k property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L345-L348
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L345-L348

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
omit hce

theorem GlobalTheory.InducedPBW.rho_zero_of_k (x : g) (hx : ∀ j, c j x = 0) (v : V) :
    rho c δ x (zv 0 v) = zv 0 (act x v) := by sorry
