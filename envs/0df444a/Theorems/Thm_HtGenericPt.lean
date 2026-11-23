-- Prove2me | Theorems.Thm_HtGenericPt
-- name    : HtGenericPt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:44:45.507926+00:00
-- url     : https://prove2.me/theorems/a2262ba8-a26b-4f20-82fe-9c5b2604164e
-- title:
--   Ht Generic Pt: Ht Generic Pt
-- statement:
--   The Ht Generic Pt construction uses the Ht Generic Pt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GenericPointHeight/GenericPointStatements/GenericPointTheorem/HtGenericPt.lean#L5-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GenericPointHeight/GenericPointStatements/GenericPointTheorem/HtGenericPt.lean#L5-L37

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointLemmas_GenericPointWeights_Wx
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointTheorem_HtGenericPt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem HtGenericPt {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by sorry
