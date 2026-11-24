-- Prove2me | Theorems.Thm_HtGaussUniq
-- name    : HtGaussUniq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:36:22.085851+00:00
-- url     : https://prove2.me/theorems/df2e3a26-c842-4b4f-95df-23c9ef9552f0
-- title:
--   Ht Gauss Uniq: Ht Gauss Uniq
-- statement:
--   The Ht Gauss Uniq construction uses the Ht Gauss Uniq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessTheorem/HtGaussUniq.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussUniqueness/GaussUniquenessStatements/GaussUniquenessTheorem/HtGaussUniq.lean#L5-L6

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessLemmas_KernelLineArguments_AdmissibleValuationPrimeSubsingleton
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussUniqueness_GaussUniquenessStatements_GaussUniquenessTheorem_HtGaussUniq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField

theorem HtGaussUniq {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.AdmissibleValuationPrimeUnique 𝒜 d := by sorry
