-- Prove2me | Theorems.Thm_GlobalTheory_T_quadraticGaussIntegral_stable_of_dual_lattice
-- name    : GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T21:13:31.343445+00:00
-- url     : https://prove2.me/theorems/877546b3-574a-4af6-8344-526b9bb9b2b6
-- title:
--   T: quadratic Gauss Integral stable of dual lattice
-- statement:
--   The T construction uses the quadratic Gauss Integral stable of dual lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticGaussIntegralStableOfDualLatticeStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticGaussIntegralStableOfDualLatticeStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticGaussIntegralStableOfDualLattice
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticGaussIntegralStableOfDualLatticeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.quadraticGaussIntegral_stable_of_dual_lattice : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (ψ : AddChar F ℂ) (x : A.K) (μ : Measure A.L), IsStdChar ψ → μ.IsAddHaarMeasure → ∀ (t : A.K) (M D : AddSubgroup A.L), IsOpen (M : Set A.L) → IsCompact (M : Set A.L) → IsOpen (D : Set A.L) → IsCompact (D : Set A.L) → (∀ m ∈ M, A.psiK ψ (t * x * A.NL m) = 1) → (D : Set A.L) = {y : A.L | ∀ m ∈ M, A.kerL ψ (t * x) y m = 1} → IsStableGauss A ψ x μ t (gaussInt A ψ x μ t (D : Set A.L)) := by sorry
