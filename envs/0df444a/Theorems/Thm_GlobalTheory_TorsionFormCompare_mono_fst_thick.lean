-- Prove2me | Theorems.Thm_GlobalTheory_TorsionFormCompare_mono_fst_thick
-- name    : GlobalTheory.TorsionFormCompare.mono_fst_thick
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:10:29.459487+00:00
-- url     : https://prove2.me/theorems/94ee08ec-f0b8-49c3-8189-2a898aa536f9
-- title:
--   Torsion Form Compare: mono fst thick
-- statement:
--   The Torsion Form Compare construction uses the mono fst thick property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUniformizationIdentityPullback.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/SameUniformizationIdentityPullback.lean#L15-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUnifRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_GmMulEqOfResMulEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SameUniformizationIdentityPullback
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TorsionFormCompare
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem GlobalTheory.TorsionFormCompare.mono_fst_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by sorry
