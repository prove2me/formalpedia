-- Prove2me | Theorems.Thm_GlobalTheory_SharpObj_per_lattice
-- name    : GlobalTheory.SharpObj.per_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:16:29.052669+00:00
-- url     : https://prove2.me/theorems/aa5dbbc0-fe29-4175-be9f-e31594b9cd33
-- title:
--   Sharp Obj: per lattice
-- statement:
--   The Sharp Obj construction uses the per lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L154-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ImInvIsHermitian.lean#L154-L214

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MulVecOfRealVecAddMemSpanPeriodLattice
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImInvIsHermitian
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SharpObj
variable {h : ℕ}
variable {τ : Matrix (Fin h) (Fin h) ℂ}

theorem GlobalTheory.SharpObj.per_lattice (hs : τ.IsSymm) (hp : (τ.map Complex.im).PosDef) :
    Function.Injective (per τ) ∧ DiscreteTopology (LinearMap.range (per τ)) ∧
      Submodule.span ℝ (LinearMap.range (per τ) : Set (Fin h → ℂ)) = ⊤ := by sorry
