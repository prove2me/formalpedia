-- Prove2me | Theorems.Thm_MasulloAudit_padic_uniformizer_difference_counterexample
-- name    : MasulloAudit.padic_uniformizer_difference_counterexample
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T02:35:45.041413+00:00
-- url     : https://prove2.me/theorems/fd7a7dd3-a865-4e4d-9cab-6e0c165e42c6
-- title:
--   A 3-adic unit residue class outside the image of the uniformizer difference
-- statement:
--   For each prime $p$, write $D_p f(x)=f(x)-f(x/p)$. If $f$ is a continuous complex function on $\mathbb Q_p$ vanishing at infinity and $D_p f$ is zero off the unit sphere, then $D_p f(u)=f(0)$ for every unit $u$. In particular, on $\mathbb Q_3$ there is a locally constant compactly supported $g$ with $g(0)=0$, $g(1)=1$, and $g(-1)=0$, lying outside the range of $D_3$ even on this larger continuous function space. Moreover $D_3g\ne D_{-3}g$. Thus on the full local Schwartz–Bruhat space the operator in Lemma 5.3.1.1 depends on the choice of uniformizer and its range is strictly smaller than $\ker\delta_0$. The manuscript later defines a modified operator separately on the unit-character components in Definition 5.3.1.2.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Chapter 5, Lemma 5.3.1.1, equation (5.3.1.1), p. 240. The modified operator of Definition 5.3.1.2 is specified on p. 241. https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf

import Mathlib

open Filter Topology
open scoped Padic

theorem MasulloAudit.padic_uniformizer_difference_counterexample :
    (∀ (p : ℕ) [Fact p.Prime] (f : ℚ_[p] → ℂ), Continuous f →
      Tendsto f (cocompact ℚ_[p]) (𝓝 0) →
      (∀ x : ℚ_[p], ‖x‖≠1 → f x-f ((p:ℚ_[p])⁻¹*x)=0) →
      ∀ u : ℚ_[p], ‖u‖=1 → f u-f ((p:ℚ_[p])⁻¹*u)=f 0) ∧
    ∃ g : ℚ_[3] → ℂ, IsLocallyConstant g ∧ HasCompactSupport g ∧ g 0=0 ∧
      g 1=1 ∧ g (-1)=0 ∧
      (∀ (f : ℚ_[3] → ℂ), Continuous f → Tendsto f (cocompact ℚ_[3]) (𝓝 0) →
        ¬∀ x : ℚ_[3], f x-f ((3:ℚ_[3])⁻¹*x)=g x) ∧
      (fun x : ℚ_[3] => g x-g ((3:ℚ_[3])⁻¹*x)) ≠
        (fun x : ℚ_[3] => g x-g ((-3:ℚ_[3])⁻¹*x)) := by sorry
