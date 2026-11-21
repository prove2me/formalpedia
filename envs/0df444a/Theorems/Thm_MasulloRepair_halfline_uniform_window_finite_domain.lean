-- Prove2me | Theorems.Thm_MasulloRepair_halfline_uniform_window_finite_domain
-- name    : MasulloRepair.halfline_uniform_window_finite_domain
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:53:38.662735+00:00
-- url     : https://prove2.me/theorems/08073a9a-4ba9-4d52-b642-bfd5c909ce25
-- title:
--   The exact finite domain of the uniform half-line window norm
-- statement:
--   Let $a\in\mathbf R$ and let $g:\mathbf R\to\mathbf R$ be measurable and nonnegative on $(0,\infty)$. For $\sigma\ge a$ write
--   $$Q_a(\sigma)=\left(\int_0^\infty g(t)\max\{t^{2a},t^{2\sigma}\}\,dt\right)^{1/2}.$$
--   The following conditions are equivalent:
--
--   1. Every displayed integrand is integrable, and there is one finite real bound $B$ with $Q_a(\sigma)\le B$ for all $\sigma\ge a$.
--   2. The endpoint density $g(t)t^{2a}$ is integrable, $g(t)=0$ for almost every $t>1$, and for every $\sigma\ge a$,
--   $$Q_a(\sigma)=\left(\int_0^\infty g(t)t^{2a}\,dt\right)^{1/2}.$$
--
--   In particular, integrability at the endpoint together with the stated support restriction is sufficient, and the uniform half-line norm is precisely the endpoint norm on this domain. For the source's density $g(t)=|\varphi(t)|^2(1+|\log t|^2)^{s/2}/t$, its positive scalar weight makes the support condition equivalent to $\varphi=0$ almost everywhere on $(1,\infty)$. This gives a repair by restricting the domain. It does not retain the original space of all exponentially decreasing smooth tests.
--
--   **Formalization Note.** Integrability is part of condition 1, so a divergent real integral cannot satisfy the finiteness condition through Lean's totalized integral convention. The theorem formalizes the general density statement; no completed Hardy--Sobolev space is defined here.
-- source:
--   Corrected replacement statements for A. M. Masullo, The Music of the Primes, Definition 9.2.2.1, equation (9.2.2.3), and Lemma 9.2.2.2(3)(a), equations (9.2.2.6)-(9.2.2.7), printed pp. 412-413; frozen draft https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . The finiteness obstruction and compact-subinterval topology alternative were reported by Yi in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2, mission 638f9b7f-e232-4624-ba08-5889465bb1e7. These are new repair lemmas, not assertions that the original unrestricted uniform-norm statement is valid. Companion to the accepted smooth-test counterexample MasulloAudit.halfline_window_norm_unbounded_on_smooth_test (a3d86692-d1d7-4198-8b9f-c526675c0e39). The exact support characterization and its proof are developed in this contribution, using monotone convergence.

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem MasulloRepair.halfline_uniform_window_finite_domain (g : ℝ → ℝ) (hg : Measurable g)
    (hgn : ∀ t : ℝ, 0 < t → 0 ≤ g t) (a : ℝ) :
    (∃ B : ℝ, ∀ σ : ℝ, a ≤ σ →
      IntegrableOn (fun t : ℝ => g t * max (t^(2*a)) (t^(2*σ))) (Ioi 0) ∧
      Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*σ))) ≤ B) ↔
    (IntegrableOn (fun t : ℝ => g t * t^(2*a)) (Ioi 0) ∧
      (∀ᵐ t : ℝ ∂volume.restrict (Ioi 1), g t = 0) ∧
      ∀ σ : ℝ, a ≤ σ →
        Real.sqrt (∫ t in Ioi (0 : ℝ), g t * max (t^(2*a)) (t^(2*σ))) =
          Real.sqrt (∫ t in Ioi (0 : ℝ), g t * t^(2*a))) := by sorry
