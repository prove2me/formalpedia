-- Prove2me | Theorems.Thm_HairerSPDE_map_add_eq_withDensity
-- name    : HairerSPDE.map_add_eq_withDensity
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:22:05.257687+00:00
-- url     : https://prove2.me/theorems/314f620b-1795-48a0-a8b9-57adc5da59c3
-- title:
--   Equation (4.14): the density $\exp(h^{*}(x)-\tfrac12\|h\|_\mu^{2})$ of a Cameron–Martin shift
-- statement:
--   **The explicit density of a translated Gaussian measure, equation (4.14).**
--
--   Let $\mu$ be a centred Gaussian measure on a separable Banach space $B$ with covariance form $C_\mu$, and let $h \in B$ admit a representer $h^{*} \in B^{*}$, i.e. a continuous linear functional with
--
--   $$ C_\mu(h^{*}, \ell) \;=\; \ell(h) \qquad \text{for all } \ell \in B^{*} $$
--
--   (Hairer's $h \in \mathring H_\mu$, for which $\|h\|_\mu^{2} = C_\mu(h^{*},h^{*})$). Then the image of $\mu$ under the translation $T_h(x) = x + h$ has an explicit density with respect to $\mu$:
--
--   $$ (T_h)_{*}\mu \;=\; D_h \cdot \mu, \qquad D_h(x) \;=\; \exp\Bigl(h^{*}(x) - \tfrac12\, C_\mu(h^{*},h^{*})\Bigr). $$
--
--   The function $D_h$ is strictly positive, $\mu$-integrable and has integral $1$, so the translated measure is not only absolutely continuous with respect to $\mu$ but equivalent to it.
--
--   This identity is the quantitative core of the forward half of the Cameron–Martin theorem: it exhibits the Radon–Nikodym derivative rather than merely asserting its existence, and it is the formula used in Girsanov-type arguments. In one dimension, with $\mu = \mathcal N(0,v)$ and $h^{*} = h/v$, it reduces to the familiar ratio $\exp(hx/v - h^{2}/2v)$ of Gaussian densities.
--
--   **Formalization Note.** The right-hand side is the measure with density $D_h$ with respect to $\mu$, the density being read as a non-negative extended-real-valued function. Only the case of a continuous representer $h^{*}$ is claimed here; a general $h \in H_\mu$ has a representer only in the $L^{2}$ sense.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 31, proof of Theorem 4.44, eq. (4.14) (case $h^{*} \in B^{*}$)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem map_add_eq_withDensity {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B, covarianceBilinDual μ h' L = L h) :
    μ.map (fun x ↦ x + h)
      = μ.withDensity
          (fun x ↦ ENNReal.ofReal (Real.exp (h' x - covarianceBilinDual μ h' h' / 2))) := by
  sorry

end HairerSPDE
