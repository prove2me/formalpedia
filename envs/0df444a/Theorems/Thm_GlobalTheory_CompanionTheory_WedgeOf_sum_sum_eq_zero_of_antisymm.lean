-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_WedgeOf_sum_sum_eq_zero_of_antisymm
-- name    : GlobalTheory.CompanionTheory.WedgeOf.sum_sum_eq_zero_of_antisymm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:33:57.450522+00:00
-- url     : https://prove2.me/theorems/8d9173bb-5f25-4cdb-b684-0550d81e1889
-- title:
--   Wedge Of: sum sum eq zero of antisymm
-- statement:
--   The Wedge Of construction uses the sum sum eq zero of antisymm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/WedgeOfSymmetricTensorZero.lean#L28-L36

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

theorem GlobalTheory.CompanionTheory.WedgeOf.sum_sum_eq_zero_of_antisymm {ι M : Type} [DecidableEq ι] [AddCommGroup M]
    (f : ι → ι → M) (hd : ∀ i, f i i = 0) (ha : ∀ i j, f i j + f j i = 0) (s : Finset ι) :
    ∑ i ∈ s, ∑ j ∈ s, f i j = 0 := by sorry
