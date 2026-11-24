-- Prove2me | Theorems.Thm_GlobalTheory_TorsLift_exists_pow_eq_unit
-- name    : GlobalTheory.TorsLift.exists_pow_eq_unit
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:53:10.724022+00:00
-- url     : https://prove2.me/theorems/231aae58-c03d-49cd-9bda-e5ee6a705f42
-- title:
--   Tors Lift: exists pow eq unit
-- statement:
--   The Tors Lift construction uses the exists pow eq unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowEqTorus.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsPowEqTorus.lean#L28-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsLiftOfRetraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
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
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
open GlobalTheory GlobalTheory.TorsLift

theorem GlobalTheory.TorsLift.exists_pow_eq_unit (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 1 ≤ n)
    (m : Γ(Sp k, ⊤)ˣ) : ∃ r : Γ(Sp k, ⊤)ˣ, r ^ n = m := by sorry
