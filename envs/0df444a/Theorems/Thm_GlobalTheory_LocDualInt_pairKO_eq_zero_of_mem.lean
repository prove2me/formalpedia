-- Prove2me | Theorems.Thm_GlobalTheory_LocDualInt_pairKO_eq_zero_of_mem
-- name    : GlobalTheory.LocDualInt.pairKO_eq_zero_of_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:11:53.697862+00:00
-- url     : https://prove2.me/theorems/305bf0f0-3bab-46d2-82d1-ba0f8b5c422e
-- title:
--   Loc Dual Int: pair KO eq zero of mem
-- statement:
--   The Loc Dual Int construction uses the pair KO eq zero of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L102-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L102-L105

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

theorem GlobalTheory.LocDualInt.pairKO_eq_zero_of_mem {a : O} {r : ℕ} {x : VT ⧸ D.T} (hx : a ^ r • x = 0) {t : ↥D.T'}
    (ht : t ∈ powSub (M := ↥D.T') a r) : pairKO D.bT D.T x t = 0 := by sorry
