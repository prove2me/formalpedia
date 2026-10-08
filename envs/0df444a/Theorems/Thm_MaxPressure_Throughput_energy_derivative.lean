-- Prove2me | Theorems.Thm_MaxPressure_Throughput_energy_derivative
-- name    : MaxPressure.Throughput.energy_derivative
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:47:53.819412+00:00
-- url     : https://prove2.me/theorems/94a185a2-ec70-41c9-8ec6-1d7bdd80325a
-- title:
--   Equations (22)–(23), p. 203 — derivative of quadratic fluid energy
-- statement:
--   For a fluid solution, the buffer vector is $\bar Z(t)=\bar Z(0)-R\bar T(t)$ at every nonnegative time. Define its quadratic energy by $f(t)=\sum_i\bar Z_i(t)^2$. At each regular time,
--
--   $$\dot f(t)=-2p(\dot{\bar T}(t),\bar Z(t)).$$
--
--   This identity relates the direction of change of the buffer levels to the pressure optimized by the policy. The equality is stated only where the fluid paths are differentiable, as in the paper.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 203, equations (21)–(23); https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Network

namespace MaxPressure.Throughput

/-- Equations (22)–(23), p. 203: the quadratic fluid energy has derivative
minus twice the network pressure at each regular time. -/
theorem energy_derivative {I J K : ℕ} (N : Network I J K)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hfluid : IsFluidSolution N Zb Tb)
    (t : ℝ) (hregular : IsRegular Zb Tb t) :
    (∀ s, 0 ≤ s → Zb s = Zb 0 - Matrix.mulVec (R N) (Tb s)) ∧
    HasDerivAt (fun s => ∑ i, Zb s i ^ 2)
      (-2 * pressure N (deriv Tb t) (Zb t)) t := by sorry

end MaxPressure.Throughput
