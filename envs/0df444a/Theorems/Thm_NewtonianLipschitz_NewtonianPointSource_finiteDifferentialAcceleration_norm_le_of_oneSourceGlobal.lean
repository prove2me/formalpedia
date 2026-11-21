-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
-- name    : NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:48:33.569506+00:00
-- url     : https://prove2.me/theorems/b6406f45-6d9d-4efd-9051-0c37303f3b3f
-- title:
--   Newtonian Point Source: finite Differential Acceleration norm le of one Source Global
-- statement:
--   R041, part 1: a proof of the global one-source C3
--   estimate would automatically imply a bound for the exact
--   finite sum of nonlinear differential accelerations.
--
--   A source at time t has initial displacement c.displacement;
--   the second position has displacement c.displacement + q.
--   Both are assumed to satisfy the same Cartesian clearance d.
--   The bound uses the sum of actual gravitational parameters,
--   with no artificial linearization and no segment assumption.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L50-L110
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L50-L110

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_of_oneSourceGlobal
    (hOne : oneSourceGlobalCandidateBound)
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d : ℝ) (hd : 0 < d) :
    (∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖) →
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        ((sources.map (fun source =>
          (source t).gravitationalParameter)).sum * candidateMaximum)) *
        ‖q‖ := by sorry
