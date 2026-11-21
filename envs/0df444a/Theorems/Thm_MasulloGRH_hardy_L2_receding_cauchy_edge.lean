-- Prove2me | Theorems.Thm_MasulloGRH_hardy_L2_receding_cauchy_edge
-- name    : MasulloGRH.hardy_L2_receding_cauchy_edge
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T04:42:46.702047+00:00
-- url     : https://prove2.me/theorems/36786d2b-d52f-4ff7-a96c-609b1519fe5a
-- title:
--   Hardy L² estimate and vanishing of receding vertical Cauchy integrals of every order
-- statement:
--   Let $\Phi:\mathbb C\to\mathbb C$, $N\ge 0$, $z\in\mathbb C$, and $u<\Re z$. If $y\mapsto\Phi(u+iy)$ belongs to $L^2(\mathbb R,dy)$, the upward vertical integral of $\Phi(s)/(s-z)^{N+1}$ over $u+i\mathbb R$ converges absolutely. Writing $d=\Re z-u$, its absolute value is at most $\|\Phi(u+i\cdot)\|_2\sqrt{\pi/d}\,d^{-N}$. Consequently, if $u_n\to-\infty$ and the vertical $L^2$ norms along $u_n$ are eventually uniformly bounded, these integrals tend to zero for every $N$ and $z$. The estimate holds for square-integrable line restrictions, with no analyticity hypothesis on $\Phi$.
-- source:
--   Alessandro Maria Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem B.2.2.4(2), p. 603, equations (B.2.2.12)–(B.2.2.13), and §9.2.2, p. 411. Gives the receding-edge estimate under uniform Hardy L² control. Companion to Prove2Me theorem 1f9c78da-5f89-4881-8840-24dea0c220bc.

import Definitions.Def_MasulloGRH_MellinRpos

open Set MeasureTheory Filter Topology MasulloGRH

theorem MasulloGRH.hardy_L2_receding_cauchy_edge (Φ : ℂ → ℂ) :
    (∀ (u : ℝ) (z : ℂ) (N : ℕ), u < z.re →
      MemLp (fun y : ℝ => Φ (u+y*Complex.I)) 2 volume →
      VerticalLineIntegrable (fun s => Φ s/(s-z)^(N+1)) u ∧
      ‖verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) u‖ ≤
        Real.sqrt (∫ y : ℝ, ‖Φ (u+y*Complex.I)‖^2) *
        Real.sqrt (Real.pi/(z.re-u)) / (z.re-u)^N) ∧
    (∀ (u : ℕ → ℝ) (M : ℝ), Tendsto u atTop atBot →
      (∀ᶠ n in atTop, MemLp (fun y : ℝ => Φ (u n+y*Complex.I)) 2 volume) →
      (∀ᶠ n in atTop, (∫ y : ℝ, ‖Φ (u n+y*Complex.I)‖^2) ≤ M) →
      ∀ (N : ℕ) (z : ℂ), Tendsto
        (fun n => verticalLineIntegral (fun s => Φ s/(s-z)^(N+1)) (u n)) atTop (𝓝 0)) := by sorry
