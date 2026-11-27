-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_exists_isIdPull
-- name    : GlobalTheory.TorsionFormCompare.exists_isIdPull
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:42:51.557369+00:00
-- url     : https://prove2.me/theorems/6144848f-9322-5416-a000-9d882c1c3ba9
-- title:
--   Torsion Form Compare: exists is Id Pull
-- statement:
--   The Torsion Form Compare construction uses the exists is Id Pull property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L44-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ExistsIdentityPullbackDegeneration.lean#L44-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatIsoUnitGenerator
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_FlatTorsionIsomorphism
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIdentityPullbackDegeneration
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

theorem GlobalTheory.TorsionFormCompare.exists_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by sorry
