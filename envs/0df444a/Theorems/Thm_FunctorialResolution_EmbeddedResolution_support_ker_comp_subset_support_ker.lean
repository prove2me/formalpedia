-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_support_ker_comp_subset_support_ker
-- name    : FunctorialResolution.EmbeddedResolution.support_ker_comp_subset_support_ker
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:54:27.565189+00:00
-- url     : https://prove2.me/theorems/41e78371-ebf7-4e8e-99d4-d982548d04a7
-- title:
--   Embedded Resolution: support ker comp subset support ker
-- statement:
--   The Embedded Resolution construction uses the support ker comp subset support ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelSupport.lean#L7-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/KernelSupport.lean#L7-L11

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_KernelSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FunctorialResolution FunctorialResolution.EmbeddedResolution
open CategoryTheory AlgebraicGeometry

theorem FunctorialResolution.EmbeddedResolution.support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by sorry
