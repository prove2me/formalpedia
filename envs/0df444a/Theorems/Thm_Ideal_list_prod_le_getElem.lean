-- Prove2me | Theorems.Thm_Ideal_list_prod_le_getElem
-- name    : Ideal.list_prod_le_getElem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:37:37.521042+00:00
-- url     : https://prove2.me/theorems/3c840709-440e-4e30-86ba-298e98a201df
-- title:
--   Ideal: list prod le get Elem
-- statement:
--   The Ideal construction uses the list prod le get Elem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L102-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/SpanSingletonProduct.lean#L102-L118

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_SpanSingletonProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal

theorem Ideal.list_prod_le_getElem {R : Type*} [CommRing R] (L : List (Ideal R)) (i : ℕ)
    (hi : i < L.length) : L.prod ≤ (L[i]'hi) := by sorry
