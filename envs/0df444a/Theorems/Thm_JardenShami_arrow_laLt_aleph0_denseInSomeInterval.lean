-- Prove2me | Theorems.Thm_JardenShami_arrow_laLt_aleph0_denseInSomeInterval
-- name    : JardenShami.arrow_laLt_aleph0_denseInSomeInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:41:18.377835+00:00
-- url     : https://prove2.me/theorems/f8a5b717-5cff-4147-9254-bf522fc4d05c
-- title:
--   Jarden Shami: arrow la Lt aleph0 dense In Some Interval
-- statement:
--   **Corollary 3.5** (Section 3, unlabelled). Let `I` be a dense linear ordering and `F` the
--   family of subsets of `I` that are dense in some interval of `I`. Then `F → (F)_{la_{<ℵ₀}}`.
--   Depends on the cited Fact 3.4, taken as the hypothesis `hfact`.
--
--   Source: https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L258-L261
-- source:
--   https://github.com/jardenadi/edge-colorings-trees-lean/blob/a213c354919238f75225b6af4bb2dac42f654449/MyResearchesLLMLean/JardenShami/Section3.lean#L258-L261

import Definitions.Def_MyResearchesLLMLean_JardenShami_Section2
import Definitions.Def_MyResearchesLLMLean_JardenShami_Section3
set_option autoImplicit true
open Cardinal
universe v w
noncomputable section
open JardenShami

theorem JardenShami.arrow_laLt_aleph0_denseInSomeInterval (I : Type w) [LinearOrder I] [DenselyOrdered I]
    (hfact : Fact_3_4.{v, w} I) :
    Arrow (denseInSomeInterval I) (denseInSomeInterval I) (laLt (ℵ₀ : Cardinal.{v})) := by sorry
