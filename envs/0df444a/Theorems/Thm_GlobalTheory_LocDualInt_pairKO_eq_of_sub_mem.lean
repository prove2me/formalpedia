-- Prove2me | Theorems.Thm_GlobalTheory_LocDualInt_pairKO_eq_of_sub_mem
-- name    : GlobalTheory.LocDualInt.pairKO_eq_of_sub_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:12:16.248087+00:00
-- url     : https://prove2.me/theorems/39c01a0c-6cb4-4e60-90c6-bab13a53bf10
-- title:
--   Loc Dual Int: pair KO eq of sub mem
-- statement:
--   The Loc Dual Int construction uses the pair KO eq of sub mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L107-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L107-L110

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
noncomputable section
open GlobalTheory GlobalTheory.LocDualInt
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    {G : Type} [Group G] [TopologicalSpace G]
    {VT VT' : Type}
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

theorem GlobalTheory.LocDualInt.pairKO_eq_of_sub_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t t' : ↥D.T'}
    (ht : t - t' ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = pairKO D.bT D.T x t' := by sorry
