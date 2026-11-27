-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_isPullGtF_self_of_isIdPull
-- name    : GlobalTheory.TorsionFormCompare.isPullGtF_self_of_isIdPull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:44:06.153335+00:00
-- url     : https://prove2.me/theorems/7e7011b2-cc56-4dc0-a337-9e8a2ef56d00
-- title:
--   Torsion Form Compare: is Pull Gt F self of is Id Pull
-- statement:
--   The Torsion Form Compare construction uses the is Pull Gt F self of is Id Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PullPointIdentityDegeneration.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/PullPointIdentityDegeneration.lean#L28-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PullPointIdentityDegeneration
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare

theorem GlobalTheory.TorsionFormCompare.isPullGtF_self_of_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (hD : IsPullDeg (RingHom.id R) D D), IsIdPull hD → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (g : GtPtF D F), IsPullGtF (RingHom.id R) hD F g g := by sorry
