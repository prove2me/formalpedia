-- Prove2me | Theorems.Thm_HtGaussGen
-- name    : HtGaussGen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:49:03.297496+00:00
-- url     : https://prove2.me/theorems/955dbe16-7315-46fc-8432-763a118ed645
-- title:
--   Ht Gauss Gen: Ht Gauss Gen
-- statement:
--   The Ht Gauss Gen construction uses the Ht Gauss Gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericTheorem/HtGaussGen.lean#L6-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/ReciprocityTheory/ReductiveGroups/ArithmeticGeometry/HeightTheory/GaussHeights/GaussGenericHeight/GaussGenericStatements/GaussGenericTheorem/HtGaussGen.lean#L6-L71

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericLemmas_TranslationDomainMaps_TranslSEquivApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GaussGenericHeight_GaussGenericStatements_GaussGenericTheorem_HtGaussGen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open MvPolynomial ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.GaussGen BlockPoly

theorem HtGaussGen {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type}
    [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type}
    [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
    [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c))
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A)
    (hx1 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.PlaceTrivialOrPositive 𝒜 d)
    (hx2 : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.AdmissibleValuationPrimeUnique 𝒜 d) :
    ReciprocityTheory.ChartRestriction.G.T0.LeafSt.GeneratorMultiHomogeneous 𝒜 d := by sorry
