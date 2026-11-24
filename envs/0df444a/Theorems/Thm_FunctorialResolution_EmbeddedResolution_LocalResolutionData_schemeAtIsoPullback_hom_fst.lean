-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_LocalResolutionData_schemeAtIsoPullback_hom_fst
-- name    : FunctorialResolution.EmbeddedResolution.LocalResolutionData.schemeAtIsoPullback_hom_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:18:43.184907+00:00
-- url     : https://prove2.me/theorems/fa22b431-7681-4f4e-9483-bdf1406c2260
-- title:
--   Local Resolution Data: scheme At Iso Pullback hom fst
-- statement:
--   The Local Resolution Data construction uses the scheme At Iso Pullback hom fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L89-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/StrongResolution/LocalResolutionData.lean#L89-L93

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_IteratedBlowups_BlowupSequenceBasic
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_StrongResolution
import Definitions.Def_Development_ResolutionOfSingularities_Foundations_BlowupUniversalProperty
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_ResolutionOfSingularities
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_StrongResolution_LocalResolutionData
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
open FunctorialResolution FunctorialResolution.EmbeddedResolution
attribute [instance] LocalResolutionData.finiteType
open FunctorialResolution.EmbeddedResolution.LocalResolutionData
variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of k)}
  [LocallyOfFiniteType f] {s : SequenceOfBlowups X}

theorem FunctorialResolution.EmbeddedResolution.LocalResolutionData.schemeAtIsoPullback_hom_fst (d : LocalResolutionData k f s) (i : d.cover.I₀) (j : ℕ)
    (hj : j ≤ (d.seq i).length) :
    (d.schemeAtIsoPullback i j hj).hom ≫ pullback.fst (d.cover.f i) (s.projectionToBase (d.reindex i j))
      = (d.seq i).projectionToBase j := by sorry
