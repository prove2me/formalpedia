-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_map_wedgeT
-- name    : GlobalTheory.CompanionTheory.WedgeOf.map_wedgeT
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:33.622468+00:00
-- url     : https://prove2.me/theorems/ef559e76-499c-491a-8eaf-ee5ee27f2338
-- title:
--   Wedge Of: map wedge T
-- statement:
--   The Wedge Of construction uses the map wedge T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L66-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L66-L75

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IotaQInjective
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_WedgeOfSymmetricTensorZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.WedgeOf
variable {R : Type} [CommRing R] {V : Type} [AddCommGroup V] [Module R V]

theorem GlobalTheory.CompanionTheory.WedgeOf.map_wedgeT {W : Type} [AddCommGroup W] [Module R W] (r : W →ₗ[R] V) (s : W ⊗[R] W) :
    exteriorPower.map 2 r (wedgeT (R := R) W s) = wedgeT (R := R) V (TensorProduct.map r r s) := by sorry
