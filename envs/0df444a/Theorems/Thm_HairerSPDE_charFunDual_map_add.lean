-- Prove2me | Theorems.Thm_HairerSPDE_charFunDual_map_add
-- name    : HairerSPDE.charFunDual_map_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T12:22:41.475463+00:00
-- url     : https://prove2.me/theorems/b4dfbdcb-019e-4737-9d65-d38d17afb2ba
-- title:
--   Characteristic function of a translated centred Gaussian on the duals
-- statement:
--   **Characteristic function of a translated centred Gaussian on the duals.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$. Then the pushforward $(T_h)_*\mu$ under $T_h(x) = x + h$ satisfies $\widehat{(T_h)_*\mu}(\ell) = \exp(i\ell(h) - C_\mu(\ell,\ell)/2)$ for every $\ell \in B^*$. This is the change-of-variables computation in the proof of Hairer's Theorem 4.44: $\int e^{i\ell(x+h)}\,d\mu = e^{i\ell(h)}\widehat{\mu}(\ell)$ with $\widehat{\mu}(\ell) = e^{-C_\mu(\ell,\ell)/2}$ for centred $\mu$.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Theorem 4.44 (Cameron-Martin), proof of the 'if' direction via characteristic functions, used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem charFunDual_map_add {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (L : StrongDual ℝ B) :
    charFunDual (μ.map (fun x : B => x + h)) L = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by sorry

end HairerSPDE
