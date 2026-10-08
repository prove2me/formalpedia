-- Prove2me | Theorems.Thm_MaxPressure_FluidStab_lyapunov_drift
-- name    : MaxPressure.FluidStab.lyapunov_drift
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T20:54:57.054935+00:00
-- url     : https://prove2.me/theorems/728648e5-059c-4473-80a3-1f51d48bc2fd
-- title:
--   Proof of Theorem 5, p. 215 — ḟ(t) = 2Ż̄·Z̄ = −2RṪ·Z̄ ≤ −2δ‖Z̄(t)‖ = −2δ√f(t)
-- statement:
--   Under the hypotheses of the previous statement (standing assumptions, a maximum pressure fluid model solution $(\bar Z,\bar T)$, $x^*\in\mathcal A$ and $\delta>0$ with $Rx^*\ge\delta e$), at every regular time $t$ the Lyapunov function $f(t)=\sum_i\bar Z_i^2(t)$ satisfies
--   $$\dot f(t)=2\dot{\bar Z}(t)\cdot\bar Z(t)=-2R\dot{\bar T}(t)\cdot\bar Z(t)\le-2\delta\|\bar Z(t)\|=-2\delta\sqrt{f(t)} .$$
--
--   This differential inequality is the core of the proof of Theorem 5: the energy decreases at a rate proportional to its square root, which forces it to reach zero in finite time.
--
--   **Formalization Note** $\|\bar Z(t)\|=\sqrt{f(t)}$ is the Euclidean norm, written as the square root of the sum of squares. The statement gives the derivative of $f$ at $t$ and the chain of (in)equalities as conjuncts.
-- source:
--   Dai & Lin, Maximum pressure policies in stochastic processing networks, Oper. Res. 53(2) (2005), p. 215, proof of Theorem 5 (App. B), second display

import Mathlib
import Definitions.Def_MaxPressure_FluidStab_Network

namespace MaxPressure.FluidStab

open Matrix

/-- Proof of Theorem 5, App. B, p. 215: under the hypotheses of `pressure_lower_bound`, at every
regular time `t` the Lyapunov function `f(t) = ∑_i Z̄_i(t)²` satisfies
`ḟ(t) = 2 Ż̄(t) · Z̄(t) = −2 R Ṫ(t) · Z̄(t) ≤ −2ε ‖Z̄(t)‖ = −2ε √f(t)`. -/
theorem lyapunov_drift {I J K : ℕ} (N : Network I J K) (hN : N.Standing)
    (Zb : ℝ → Fin I → ℝ) (Tb : ℝ → Fin J → ℝ)
    (hsol : IsFluidSolution N Zb Tb) (hmp : MPFluidEq N Zb Tb)
    (xs : Fin J → ℝ) (hxs : xs ∈ allocSet N) (ε : ℝ) (hε : 0 < ε)
    (hR : ∀ i, ε ≤ (R N *ᵥ xs) i) (t : ℝ) (ht : IsRegular Zb Tb t) :
    HasDerivAt (fun s => ∑ i, Zb s i ^ 2) (2 * (deriv Zb t ⬝ᵥ Zb t)) t ∧
    2 * (deriv Zb t ⬝ᵥ Zb t) = -2 * pressure N (deriv Tb t) (Zb t) ∧
    -2 * pressure N (deriv Tb t) (Zb t) ≤ -2 * ε * Real.sqrt (∑ i, Zb t i ^ 2) := by sorry

end MaxPressure.FluidStab
