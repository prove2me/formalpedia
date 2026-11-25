-- Prove2me | Theorems.Thm_GlobalTheory_LB_coord_isoOfGen_hom_app
-- name    : GlobalTheory.LB.coord_isoOfGen_hom_app
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:51.026893+00:00
-- url     : https://prove2.me/theorems/b6d3126f-968f-45ad-b362-b5196da93c08
-- title:
--   LB: coord iso Of Gen hom app
-- statement:
--   The LB construction uses the coord iso Of Gen hom app property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L596-L602
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/QuasicoherentCohomology/BijectiveSmulChartSec.lean#L596-L602

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_LinCombTrivG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThetaVV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_AppCompatGeneric
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniformBaseChange_Transport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SpanSingletonEqTopIffIsUnitOfIsBaseChange
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_BijectiveSmulChartSec
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
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.LB
variable {X Y : Scheme.{0}}
variable (L : LB X)
variable {L}
variable {M : LB X}

theorem GlobalTheory.LB.coord_isoOfGen_hom_app (hL : L.IsLB) (hM : M.IsLB) (w : LB.Iso L M) (hw : w.IsGen)
    {V : X.Opens} (s : Γ(toMod L, V)) (p : M.ι) (q : L.ι) {W : X.Opens}
    (hp : W ≤ V ⊓ M.U p) (hq : W ≤ V ⊓ L.U q) (h : W ≤ M.U p ⊓ L.U q) :
    resG X hp (coord ((isoOfGen hL hM w hw).hom.app V s) p) =
      resG X h ((show Γ(X, M.U p ⊓ L.U q)ˣ from w.s (p, q)) : Γ(X, M.U p ⊓ L.U q)) *
        resG X hq (coord s q) := by sorry
