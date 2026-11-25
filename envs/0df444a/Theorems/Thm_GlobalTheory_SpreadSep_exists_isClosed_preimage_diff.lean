-- Prove2me | Theorems.Thm_GlobalTheory_SpreadSep_exists_isClosed_preimage_diff
-- name    : GlobalTheory.SpreadSep.exists_isClosed_preimage_diff
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:44:24.24654+00:00
-- url     : https://prove2.me/theorems/10d5c722-28f3-49b5-96cd-2bcb2bb3b260
-- title:
--   Spread Sep: exists is Closed preimage diff
-- statement:
--   The Spread Sep construction uses the exists is Closed preimage diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFgIsSeparated.lean#L14-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFgIsSeparated.lean#L14-L104

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_MorphismsSpreadOutToFgSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsFgIsSeparated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SpreadSep
universe u
open AlgebraicGeometry CategoryTheory Limits

theorem GlobalTheory.SpreadSep.exists_isClosed_preimage_diff {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
    (hc : IsLimit c) [IsCofiltered I] [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)] {i : I}
    (O O' : (D.obj i).Opens) (hO : IsCompact (O : Set (D.obj i)))
    (hO' : IsCompact (O' : Set (D.obj i)))
    (H : IsClosed (c.π.app i ⁻¹' ((O : Set (D.obj i)) \ O'))) :
    ∃ (j : I) (f : j ⟶ i), IsClosed (D.map f ⁻¹' ((O : Set (D.obj i)) \ O')) := by sorry
