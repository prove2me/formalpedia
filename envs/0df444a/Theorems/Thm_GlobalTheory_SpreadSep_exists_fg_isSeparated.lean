-- Prove2me | Theorems.Thm_GlobalTheory_SpreadSep_exists_fg_isSeparated
-- name    : GlobalTheory.SpreadSep.exists_fg_isSeparated
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T15:02:13.605829+00:00
-- url     : https://prove2.me/theorems/769fff7f-e558-55da-bca0-82380c526813
-- title:
--   Spread Sep: exists fg is Separated
-- statement:
--   The Spread Sep construction uses the exists fg is Separated property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFgIsSeparated.lean#L183-L256
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsFgIsSeparated.lean#L183-L256

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

theorem GlobalTheory.SpreadSep.exists_fg_isSeparated (k V : Type) [CommRing k] [IsNoetherianRing k] [CommRing V]
    [Algebra k V] (X : Scheme.{0}) (p : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) (h₁ : LocallyOfFiniteType p) (h₂ : QuasiCompact p)
    (h : IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k V)))) :
    ∃ R : Subalgebra k V, R.FG ∧ IsSeparated (pullback.snd p (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap k R))) := by sorry
