-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_wedgeT_tmul_self
-- name    : GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_self
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:44.728565+00:00
-- url     : https://prove2.me/theorems/62a2543c-91e1-4e0d-8eb3-a07e050b06fd
-- title:
--   Wedge Of: wedge T tmul self
-- statement:
--   The Wedge Of construction uses the wedge T tmul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L16-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L16-L19

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

theorem GlobalTheory.CompanionTheory.WedgeOf.wedgeT_tmul_self (a : V) : wedgeT (R := R) V (a ⊗ₜ[R] a) = 0 := by sorry
