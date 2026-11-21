-- Prove2me | Theorems.Thm_NewtonianLipschitz_NewtonianPointSource_finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
-- name    : NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:49:01.511483+00:00
-- url     : https://prove2.me/theorems/c0b629aa-92d6-42d0-be1c-aeb16703ce8a
-- title:
--   Newtonian Point Source: finite Differential Acceleration norm le length mul of one Source Global
-- statement:
--   R041, part 2: once the one-source global sharp estimate
--   is proved, N point sources with parameters at most M have
--   the sought N*M*C3/d³ coefficient for the exact sum.
--   This theorem is CONDITIONAL on hOne; it does not prove hOne.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L144-L174
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L144-L174

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.NewtonianPointSource.finiteDifferentialAcceleration_norm_le_length_mul_of_oneSourceGlobal
    (hOne : oneSourceGlobalCandidateBound)
    (sources : List (ℝ → NewtonianPointSource))
    (t : ℝ) (q : Vec3) (d M : ℝ) (hd : 0 < d)
    (hsafe : ∀ source ∈ sources,
      d ≤ ‖(source t).displacement‖ ∧
      d ≤ ‖(source t).displacement + q‖)
    (hcap : ∀ source ∈ sources,
      (source t).gravitationalParameter ≤ M) :
    ‖NewtonianPointSource.finiteDifferentialAcceleration sources t q‖ ≤
      ((1 / d ^ 3) *
        (((sources.length : ℝ) * M) * candidateMaximum)) * ‖q‖ := by sorry
