-- Prove2me | Theorems.Thm_K24_Global_FlatTorus_projectedDefect_holder_bounds
-- name    : K24.Global.FlatTorus.projectedDefect_holder_bounds
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:28:31.632774+00:00
-- url     : https://prove2.me/theorems/bf3dbd1f-9e38-467e-a2e2-51297a411ee6
-- title:
--   K24: finite C1 Holder norm and sharp positive lower bound for the actual projected defect
-- statement:
--   For every original CircleAction rho on the original flat torus whose action map is exactly translate, and every original HolderExponent alpha, the original order-one extended Holder norm of projectedDefect rho alpha n is finite for all natural n. For every n >= 2, the original real order-one Holder norm is at least Real.rpow Real.pi (-alpha). All geometric coefficient identities and the actual Haar projection identity are proved in the supplied source. No desired norm estimate, regularity, coefficient identity, or projection equality is an added assumption. These are exactly the projected-defect norm clauses of the original sharpness analytic residual.
-- source:
--   Original full K24 root aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22, source Git commit 8c02be189f097080feca952347c9104bfb986242. Frozen original definition node 9140e2e8-3049-4225-86fe-cfe1a8c49825. Directly discharges the two defect norm clauses of sharpness_analytic 9c6a6e33-1818-46c7-910f-1917ab540986.

import Definitions.Def_K24GlobalStatement
set_option autoImplicit false
open Filter Topology
open scoped Manifold ContDiff NNReal ENNReal Matrix.Norms.Elementwise

namespace K24.Global.FlatTorus
theorem projectedDefect_holder_bounds :
  ∀ (rho : CircleAction Torus), rho.act = translate → ∀ alpha : HolderExponent,
    (∀ n : ℕ, covectorHolderENorm 1 alpha.value (projectedDefect rho alpha.value n) < ⊤) ∧
    (∀ n : ℕ, 2 ≤ n → Real.rpow Real.pi (-(alpha.value : ℝ)) ≤
      covectorHolderNorm 1 alpha.value (projectedDefect rho alpha.value n)) := by
  sorry
end K24.Global.FlatTorus
