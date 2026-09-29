-- Prove2me | Theorems.Thm_HairerSPDE_norm_le_cameronMartinNorm
-- name    : HairerSPDE.norm_le_cameronMartinNorm
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-12T21:20:57.313012+00:00
-- url     : https://prove2.me/theorems/3fcdd46a-9da5-4deb-a1f1-ba6613ce597a
-- title:
--   Proposition 4.32: $\|h\|^2 \le \|C_\mu\|\,\|h\|_\mu^2$
-- statement:
--   **Proposition 4.32: the Cameron–Martin space embeds continuously in $B$.**
--
--   Let $\mu$ be a centred Gaussian measure on a separable Banach space $B$ and let $C_\mu$ be its covariance form on $B^{*}$. By Corollary 4.14 the form is bounded: there is a constant $C \ge 0$ with
--
--   $$ C_\mu(\ell_1, \ell_2) \;\le\; C\,\|\ell_1\|\,\|\ell_2\| \qquad \text{for all } \ell_1, \ell_2 \in B^{*}, $$
--
--   and $\|C_\mu\|$ denotes the smallest such constant. The claim is the bound (4.11): for every $h \in B$ and every $r \ge 0$,
--
--   $$ \|h\|_\mu \le r \quad \Longrightarrow \quad \|h\| \;\le\; \sqrt{C}\; r, $$
--
--   equivalently $\|h\|^{2} \le \|C_\mu\|\,\|h\|_\mu^{2}$ for all $h$ of finite Cameron–Martin norm.
--
--   The consequence Hairer draws is that $H_\mu$ really is a subspace of $B$ rather than an abstract completion sitting outside it, and that its norm dominates the ambient norm; in particular $\|h\|_\mu = 0$ forces $h = 0$ whenever the covariance form is bounded, so $\|\cdot\|_\mu$ is a genuine norm on $H_\mu$.
--
--   **Formalization Note.** The bounding constant $C$ of Corollary 4.14 is taken as an explicit hypothesis rather than as an operator norm, and the bound on the Cameron–Martin norm is expressed through a non-negative real $r$ dominating it; this keeps the statement inside the real numbers while covering every $h$ with $\|h\|_\mu < \infty$.
-- source:
--   M. Hairer, *An Introduction to Stochastic PDEs*, lecture notes, arXiv:0907.4178v2 (3 Jul 2023), p. 28, Proposition 4.32 (eq. (4.11)); bound of Corollary 4.14, p. 22

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

theorem norm_le_cameronMartinNorm {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (C : ℝ) (hC : ∀ L₁ L₂ : StrongDual ℝ B, covarianceBilinDual μ L₁ L₂ ≤ C * ‖L₁‖ * ‖L₂‖)
    (h : B) (r : ℝ≥0) (hr : cameronMartinNorm μ h ≤ r) :
    ‖h‖ ≤ Real.sqrt C * r := by sorry

end HairerSPDE
