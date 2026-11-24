-- Prove2me | Theorems.Thm_FunctorialResolution_EmbeddedResolution_exists_affine_etale_cover_pullback_sigmaOpensDesc
-- name    : FunctorialResolution.EmbeddedResolution.exists_affine_etale_cover_pullback_sigmaOpensDesc
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:47:02.366723+00:00
-- url     : https://prove2.me/theorems/5ccda146-0257-4868-861e-9b387aaa2aa3
-- title:
--   Embedded Resolution: exists affine etale cover pullback sigma Opens Desc
-- statement:
--   The Embedded Resolution construction uses the exists affine etale cover pullback sigma Opens Desc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L105-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/ResolutionOfSingularities/EmbeddedResolution/AlgebraicPreliminaries/DisjointUnionOfOpensPullback.lean#L105-L128

import Mathlib
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpens
import Definitions.Def_Development_ResolutionOfSingularities_EmbeddedResolution_AlgebraicPreliminaries_DisjointUnionOfOpensPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FunctorialResolution FunctorialResolution.EmbeddedResolution
universe u

theorem FunctorialResolution.EmbeddedResolution.exists_affine_etale_cover_pullback_sigmaOpensDesc {k : Type u} [Field k]
    (Y : Scheme.{u}) (p : Y ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType p] [QuasiCompact p]
    {ι : Type u} [Finite ι] (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (W' : Scheme.{u}) [IsAffine W'] [IsReduced W'] (q : W' ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType q] [QuasiCompact q] (g' : W' ⟶ Y) [Etale g'] (_hg : g' ≫ p = q) :
    ∃ (V : Scheme.{u}) (s : V ⟶ Spec (CommRingCat.of k))
      (r : V ⟶ pullback g' (sigmaOpensDesc Y U)),
      IsAffine V ∧ IsReduced V ∧ LocallyOfFiniteType s ∧ QuasiCompact s ∧
        Etale r ∧ Surjective r ∧
        r ≫ pullback.fst g' (sigmaOpensDesc Y U) ≫ q = s := by sorry
