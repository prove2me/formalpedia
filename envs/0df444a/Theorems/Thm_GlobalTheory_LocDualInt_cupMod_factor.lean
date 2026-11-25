-- Prove2me | Theorems.Thm_GlobalTheory_LocDualInt_cupMod_factor
-- name    : GlobalTheory.LocDualInt.cupMod_factor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:13:35.099656+00:00
-- url     : https://prove2.me/theorems/954a1dae-d974-5150-b487-8945cd32bfbe
-- title:
--   Loc Dual Int: cup Mod factor
-- statement:
--   The Loc Dual Int construction uses the cup Mod factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L112-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FactorMemCocyclesPowQuot.lean#L112-L125

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

theorem GlobalTheory.LocDualInt.cupMod_factor {c : G → VT ⧸ D.T} {a : O} {r m n : ℕ} (hc : ∀ g, a ^ r • c g = 0)
    (hrm : r ≤ m) (hmn : m ≤ n) (z : G → ↥D.T' ⧸ powSub (M := ↥D.T') a n) :
    cupMod D c a m (fun g => Submodule.factor (powSub_anti (M := ↥D.T') a hmn) (z g)) =
      cupMod D c a n z := by sorry
