-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_44
-- name    : LatticeHamSim.StrictLR.eq_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:06.98104+00:00
-- url     : https://prove2.me/theorems/7b49b1dc-a11a-4199-bae4-393e81836baa
-- title:
--   (44), p. 26 — C_B(X,t) ≤ 2‖B‖(2|t|)^ℓ/ℓ! Σ_{Z₁,…,Z_ℓ linked} Π‖h_{Z_j}‖, ℓ = ⌊dist(X,Y)⌋, strictly local h
-- statement:
--   Let $H = \sum_{X \subseteq \Lambda} h_X$ be a Hamiltonian on a finite metric space of sites $\Lambda$ with local dimension $q$, where every $h_X$ is Hermitian and supported on $X$, and assume **strict locality**: $h_X = 0$ whenever $\mathrm{diam}(X) > 1$. Let $B$ be an operator supported on a set $Y$ of sites, let $X$ be a set of sites, and put $\ell = \lfloor \mathrm{dist}(X, Y) \rfloor$. Then for every real $t$,
--   $$C_B(X, t) \le 2\|B\|\, \frac{(2|t|)^{\ell}}{\ell!} \sum_{Z_1, \dots, Z_\ell \,:\, \text{linked}} \ \prod_{j=1}^{\ell} \|h_{Z_j}\|,$$
--   where the sum is over all $\ell$-tuples of sets of sites with $X \sim Z_1 \sim \cdots \sim Z_\ell$ (for $\ell = 0$ the sum is $1$ and the bound reads $C_B(X, t) \le 2\|B\|$).
--
--   The lower-order terms of the iterated inequality (43) vanish because a chain of fewer than $\ell$ overlapping sets of diameter at most $1$ cannot connect $X$ to $Y$; this display is what remains.
--
--   **Formalization Note** $\ell$ is the natural-number floor of `setDist X Y` (which is $0$ if $X$ or $Y$ is empty). The statement is for every real $t$, with $|t|$ as on the page. $\|\cdot\|$ is the $L^2$ operator norm. Diameters are `Metric.diam` of the finite set.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 26, Appendix C.4, display (44) (the last line of the chain (42)–(44)) and the text following it on pp. 26–27

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_44 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X Y : Finset Λ) (hB : LatticeHamSim.CommLR.SupportedOn Y B) (t : ℝ) :
    LatticeHamSim.CommLR.CB h B X t ≤ 2 * ‖B‖ * (2 * |t|) ^ ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ / (⌊LatticeHamSim.CommLR.setDist X Y⌋₊).factorial *
      linkedSum h X ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ := by sorry

end LatticeHamSim.StrictLR
