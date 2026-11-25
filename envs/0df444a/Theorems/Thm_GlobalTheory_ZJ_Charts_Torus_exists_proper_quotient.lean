-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_Charts_Torus_exists_proper_quotient
-- name    : GlobalTheory.ZJ.Charts.Torus.exists_proper_quotient
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T17:30:02.620538+00:00
-- url     : https://prove2.me/theorems/5e0a44be-e785-5ffb-a3f1-a7489725ec32
-- title:
--   Torus: exists proper quotient
-- statement:
--   The Torus construction uses the exists proper quotient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L141-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/MemRangeAppLEChartIff.lean#L141-L152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsAffineSplitTorusLeft
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_IsClosedImmersionIffPullRatio
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_AbProj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemRangeAppLEChartIff
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
open GlobalTheory.ZJ
noncomputable section
open GlobalTheory GlobalTheory.ZJ
open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs

theorem GlobalTheory.ZJ.Charts.Torus.exists_proper_quotient :
    ∀ (K : Type) [Field K] (H : Over (Sp K)) [GrpObj H] [IsCommMonObj H] [Smooth H.hom] [IsSeparated H.hom] [QuasiCompact H.hom] (C : Charts H.left) (d : ℕ) (c : Fin d → C.Cl) (i : splitTorus (Sp K) (Fin d → ℤ) ⟶ H), C.Torus c i → ∃ (B : Over (Sp K)) (q : H ⟶ B), IsProper B.hom ∧ IsAffineHom q.left ∧ ∃ V : {i // C.wt i = C.c₀} → B.left.Opens, ⨆ a, V a = ⊤ ∧ ∀ a, IsAffineOpen (V a) ∧ ∃ h : C.W a = q.left ⁻¹ᵁ V a, Function.Injective (q.left.appLE (V a) (C.W a) h.le).hom ∧ ∀ u, HasWt i (C.W a) u 0 ↔ u ∈ Set.range (q.left.appLE (V a) (C.W a) h.le).hom := by sorry
