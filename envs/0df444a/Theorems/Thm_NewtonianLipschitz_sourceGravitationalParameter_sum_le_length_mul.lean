-- Prove2me | Theorems.Thm_NewtonianLipschitz_sourceGravitationalParameter_sum_le_length_mul
-- name    : NewtonianLipschitz.sourceGravitationalParameter_sum_le_length_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T03:49:12.752175+00:00
-- url     : https://prove2.me/theorems/f1460d36-ca49-4ba9-bb59-9f1cd181e26b
-- title:
--   Newtonian Lipschitz: source Gravitational Parameter sum le length mul
-- statement:
--   Elementary finite-list cap on the sum of physical
--   gravitational parameters: each parameter at most M
--   implies total parameter at most N*M.
--
--   Source: https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L115-L138
-- source:
--   https://github.com/alexodas/NewtonianLipschitzOptimality/blob/74f12a8510a4b0087b56f2b309e6ad99fbd26420/NewtonianLipschitz/ConditionalFiniteSource.lean#L115-L138

module
public import Definitions.Def_NewtonianLipschitz_CrossFaceTwoHop
public import Definitions.Def_NewtonianLipschitz_FiniteSources
public import Definitions.Def_NewtonianLipschitz_ConditionalFiniteSource
set_option autoImplicit true
@[expose] public section
public section
open NewtonianLipschitz

theorem NewtonianLipschitz.sourceGravitationalParameter_sum_le_length_mul
    (sources : List (ℝ → NewtonianPointSource))
    (t M : ℝ) :
    (∀ source ∈ sources,
      (source t).gravitationalParameter ≤ M) →
    (sources.map (fun source =>
      (source t).gravitationalParameter)).sum ≤
        (sources.length : ℝ) * M := by sorry
