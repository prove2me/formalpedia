-- Prove2me | Theorems.Thm_HairerSPDE_map_eq_gaussianReal_of_tendsto
-- name    : HairerSPDE.map_eq_gaussianReal_of_tendsto
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:21:22.547714+00:00
-- url     : https://prove2.me/theorems/03af751e-95a0-4c58-8a53-a99d96edc884
-- title:
--   Proposition 4.40: elements of the reproducing kernel are centred Gaussian
-- statement:
--   **Proposition 4.40: the law of an element of the reproducing kernel space.**
--
--   Let $\mu$ be a centred Gaussian measure on a separable Banach space $B$. The reproducing kernel $R_\mu$ of $\mu$ is the closure of $B^{*}$ inside $L^{2}(B,\mu)$; its elements are therefore $L^{2}(\mu)$-limits of continuous linear functionals, and are in general not continuous themselves. The claim is that such a limit is again a centred Gaussian variable whose variance is its $L^{2}$ norm.
--
--   Precisely: let $f \in L^{2}(B,\mu)$ and let $(\ell_n)_{n \in \mathbb N}$ be a sequence in $B^{*}$ with
--
--   $$ \int_B \bigl(\ell_n(x) - f(x)\bigr)^{2}\, \mu(dx) \;\xrightarrow[n\to\infty]{}\; 0 . $$
--
--   Then the law of $f$ under $\mu$ is the centred Gaussian law on $\mathbb R$ with variance $\int_B f(x)^{2}\,\mu(dx)$:
--
--   $$ f_{*}\mu \;=\; \mathcal N\Bigl(0,\ \int_B f^{2}\,d\mu\Bigr). $$
--
--   Applied to $f = h^{*}$, the reproducing-kernel element attached to $h \in H_\mu$, this is Hairer's statement that $h^{*}$ has law $\mathcal N(0, \|h\|_\mu^{2})$; it is what makes the exponential density of the Cameron–Martin theorem integrable with total mass one, and by polarisation it also gives the covariance $\mathbb E[h^{*}k^{*}] = \langle h, k\rangle_\mu$.
--
--   **Formalization Note.** The variance is read off as the (non-negative) second moment of $f$; the degenerate case of a $\mu$-almost surely vanishing limit is included, the law then being the Dirac mass at $0$, which is the Gaussian law with variance $0$.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 30, Proposition 4.40 (with the reproducing kernel $R_\mu$ of Proposition 4.34, p. 29)

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem map_eq_gaussianReal_of_tendsto {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (f : B → ℝ) (hf : MemLp f 2 μ) (L : ℕ → StrongDual ℝ B)
    (hL : Tendsto (fun n ↦ ∫ x, (L n x - f x) ^ 2 ∂μ) atTop (𝓝 0)) :
    μ.map f = gaussianReal 0 (∫ x, (f x) ^ 2 ∂μ).toNNReal := by sorry

end HairerSPDE
