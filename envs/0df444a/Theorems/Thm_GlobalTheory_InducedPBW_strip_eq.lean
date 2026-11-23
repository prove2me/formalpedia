-- Prove2me | Theorems.Thm_GlobalTheory_InducedPBW_strip_eq
-- name    : GlobalTheory.InducedPBW.strip_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:44.644808+00:00
-- url     : https://prove2.me/theorems/0b488d72-7bea-43f5-ada1-1557afaa1ff7
-- title:
--   Induced PBW: strip eq
-- statement:
--   The Induced PBW construction uses the strip eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L254-L255
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DegreeSingleAdd.lean#L254-L255

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
omit hce [Fintype ι] [LinearOrder ι]

theorem GlobalTheory.InducedPBW.strip_eq {s : Finset ι} {x : g} (hx : ∀ j ∈ s, c j x = 0) : strip e c s x = x := by sorry
