-- Prove2me | Theorems.Thm_GlobalTheory_LocDualInt_smul_mem_powSub
-- name    : GlobalTheory.LocDualInt.smul_mem_powSub
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:19:24.108242+00:00
-- url     : https://prove2.me/theorems/2549f25e-eeb7-5e8c-a394-bc10f37a757b
-- title:
--   Loc Dual Int: smul mem pow Sub
-- statement:
--   The Loc Dual Int construction uses the smul mem pow Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L19-L20

import Mathlib
import Definitions.Def_Formalism_WachLatticeTwists_LatticeDualFibres_FibreDualStable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FactorMemCocyclesPowQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.RepresentationBoundsCohomology.LOC ReciprocityTheory.Gal
open Formalism.NG (KO)
noncomputable section
open GlobalTheory GlobalTheory.LocDualInt
variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem GlobalTheory.LocDualInt.smul_mem_powSub (a : O) (n : ℕ) (y : M) : a ^ n • y ∈ powSub (M := M) a n := by sorry
