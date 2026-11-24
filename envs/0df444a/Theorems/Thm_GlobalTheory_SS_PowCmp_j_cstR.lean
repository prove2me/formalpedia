-- Prove2me | Theorems.Thm_GlobalTheory_SS_PowCmp_j_cstR
-- name    : GlobalTheory.SS.PowCmp.j_cstR
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T19:37:01.151249+00:00
-- url     : https://prove2.me/theorems/93825e45-5cb2-4a11-b171-376f3a39a0e1
-- title:
--   Pow Cmp: j cst R
-- statement:
--   The Pow Cmp construction uses the j cst R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LeOfZpowMulUnitEq.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/LeOfZpowMulUnitEq.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_LeOfZpowMulUnitEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.PowCmp
variable {R : Type} [CommRing R] {K : Type} [Field K] [Algebra R K] {A : Over (Sp K)}

theorem GlobalTheory.SS.PowCmp.j_cstR (M : Model R A) (U : M.Y.left.Opens) (r : R) :
    (M.j.app U).hom (cstR M U r) = cstK A _ (algebraMap R K r) := by sorry
