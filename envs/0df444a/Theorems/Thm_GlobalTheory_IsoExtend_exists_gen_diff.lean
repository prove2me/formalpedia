-- Prove2me | Theorems.Thm_GlobalTheory_IsoExtend_exists_gen_diff
-- name    : GlobalTheory.IsoExtend.exists_gen_diff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:16:35.186738+00:00
-- url     : https://prove2.me/theorems/27491b9a-3f34-495d-9477-052750f0af19
-- title:
--   Iso Extend: exists gen diff
-- statement:
--   The Iso Extend construction uses the exists gen diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LineBundleIsoExtendOfNormalBase.lean#L99-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LineBundleIsoExtendOfNormalBase.lean#L99-L122

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LineBundleIsoExtendOfNormalBase
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.IsoExtend
variable {X Y Y' : Scheme.{0}}

theorem GlobalTheory.IsoExtend.exists_gen_diff (S : Scheme.{0}) [IsIntegral S] [IsLocallyNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S)
    (U H HU : Scheme.{0}) [Nonempty U] (j : U ⟶ S) [IsOpenImmersion j] (p : H ⟶ S) (e : S ⟶ H) (jH : HU ⟶ H)
    (pU : HU ⟶ U) (hp : Smooth p) (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _) (sq : IsPullback jH pU p j)
    {D : LB H} (hD : D.IsLB) (H₀ : ∃ t : LB.Gen (D.pull jH), t.IsGen) :
    ∃ c : LB.Gen (LB.LinComb D ![𝟙 H, p ≫ e] ![1, -1]), c.IsGen := by sorry
