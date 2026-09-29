-- Prove2me | Theorems.Thm_HairerSPDE_map_add_exists_pos_withDensity_of_finite_norm
-- name    : HairerSPDE.map_add_exists_pos_withDensity_of_finite_norm
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-14T11:35:09.633534+00:00
-- url     : https://prove2.me/theorems/2c7066f5-e754-4ff2-bad7-0cbbf19fecdd
-- title:
--   Cameron-Martin density: finite-norm translates have a strictly positive density
-- statement:
--   **The Cameron-Martin density of a finite-norm translate.** Let $B$ be a separable Banach space, $\mu$ a centred Gaussian Borel measure on $B$, and $h \in B$ a point of finite Cameron-Martin norm, $\|h\|_\mu \neq \infty$. Write $T_h(x) = x + h$. Then the push-forward $(T_h)_*\mu$ has a density with respect to $\mu$ that is everywhere strictly positive: there is a measurable $f : B \to [0,\infty]$ with $f(x) \neq 0$ for every $x \in B$ and
--
--   $$ (T_h)_*\mu = f \cdot \mu . $$
--
--   Hairer proves this (Theorem 4.44, the 'if' direction) with the explicit density
--
--   $$ f(x) = \exp\!\Bigl(h^{*}(x) - \tfrac12 \|h\|_\mu^{2}\Bigr), $$
--
--   where $h^{*} \in \mathcal{R}_\mu \subset L^{2}(B,\mu)$ is the reproducing-kernel element of $h$ (equation (4.14) of the notes). Because the exponent is finite and the exponential is everywhere positive, $f$ vanishes nowhere; the measure equality is therefore an equality of a measure with a strictly positive density. The statement is the strictly stronger, positive-density form of the Cameron-Martin absolute continuity used in the proof of Proposition 4.45: it is equivalent to $\mu$ and $(T_h)_*\mu$ being mutually absolutely continuous, and it implies that the two measures have exactly the same null sets.
-- source:
--   M. Hairer, An Introduction to Stochastic PDEs, arXiv:0907.4178v2, Theorem 4.44 (Cameron-Martin) and equation (4.14), used in the proof of Proposition 4.45, p. 32.

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem map_add_exists_pos_withDensity_of_finite_norm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B)
    (hh : cameronMartinNorm μ h ≠ ∞) :
    ∃ f : B → ℝ≥0∞, Measurable f ∧ (∀ x : B, f x ≠ 0) ∧
      μ.map (fun x : B => x + h) = μ.withDensity f := by sorry

end HairerSPDE
