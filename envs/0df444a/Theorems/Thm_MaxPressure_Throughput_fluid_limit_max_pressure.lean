-- Prove2me | Theorems.Thm_MaxPressure_Throughput_fluid_limit_max_pressure
-- name    : MaxPressure.Throughput.fluid_limit_max_pressure
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:03:00.166989+00:00
-- url     : https://prove2.me/theorems/408f28d9-7f72-4c3e-94a1-97835829cbd4
-- title:
--   Lemma 4, p. 213 — maximum-pressure fluid equation (20)
-- statement:
--   Consider a preemptive, processor-splitting maximum-pressure process satisfying EAA and the network equations. On a sample path where the primitive limits (3)–(4) hold, let $(\bar Z,\bar T)$ be any fluid limit. At each positive regular time $t$, its instantaneous activity allocation attains the greatest pressure among the extreme allocations:
--
--   $$p(\dot{\bar T}(t),\bar Z(t))=\max_{a\in\mathcal E}p(a,\bar Z(t)).$$
--
--   This supplies the policy equation that distinguishes maximum-pressure fluid limits from those of a general service policy. Regularity means that both fluid paths are differentiable at $t$.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 213, Lemma 4; equation (20) p. 203; proof p. 214; https://doi.org/10.1287/opre.1040.0170

import Mathlib
import Definitions.Def_MaxPressure_Throughput_Dynamics

namespace MaxPressure.Throughput

/-- Lemma 4, p. 213: every fluid limit of the maximum-pressure process
satisfies fluid equation (20). -/
theorem fluid_limit_max_pressure {I J K : ℕ} {Ω : Type*}
    (N : Network I J K) (hN : N.Standing) (hEAA : EAA N)
    (E : Finset (Fin J → ℝ)) (hE : (E : Set (Fin J → ℝ)) = extremeAllocs N)
    (P : Primitives I J Ω) (Z : Ω → ℝ → Fin I → ℝ)
    (Ta : Ω → (Fin J → ℝ) → ℝ → ℝ) (ω : Ω)
    (heq : NetworkEquations N P Z (activityTime E Ta) ω)
    (hmp : MPProcess N E Z Ta ω)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hlim : IsFluidLimit N P Z (activityTime E Ta) ω Zb Tb) :
    MPFluidEq N Zb Tb := by sorry

end MaxPressure.Throughput
