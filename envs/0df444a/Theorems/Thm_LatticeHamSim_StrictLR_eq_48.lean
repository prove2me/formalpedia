-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_48
-- name    : LatticeHamSim.StrictLR.eq_48
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:56.632189+00:00
-- url     : https://prove2.me/theorems/7ee34156-5885-4ab1-a6d9-ba990d0e6c7a
-- title:
--   (48), p. 27 — ‖[A_X(t),B_Y]‖ ≤ 2‖A‖‖B‖|X|(2ζ₀|t|)^ℓ/ℓ! with ℓ = ⌊dist(X,Y)⌋ for strictly local H
-- statement:
--   Let $\Lambda$ be a finite metric space of sites, each carrying $\mathbb{C}^q$, and let $H = \sum_{X \subseteq \Lambda} h_X$, where every $h_X$ is Hermitian and supported on $X$. Assume **strict locality**, $h_X = 0$ whenever $\mathrm{diam}(X) > 1$, and let $\zeta_0$ satisfy
--   $$\sum_{Q \ni x} |Q|\, \|h_Q\| \le \zeta_0 \quad \text{for every site } x .$$
--   Let $A$ be an operator supported on $X$ and $B$ an operator supported on $Y$, write $A(t) = e^{iHt} A e^{-iHt}$, and put $\ell = \lfloor \mathrm{dist}(X, Y) \rfloor$. Then for every real $t$,
--   $$\big\|[A(t), B]\big\| \le 2\, \|A\|\, \|B\|\, |X|\, \frac{(2\zeta_0 |t|)^{\ell}}{\ell!} .$$
--
--   This is the Lieb–Robinson bound for strictly local interactions: the commutator of an evolved local operator with a distant one is suppressed by the factor $(2\zeta_0|t|)^{\ell}/\ell!$, which at fixed time decays faster than exponentially in the distance.
--
--   **Formalization Note** The paper's $\zeta_0 = \max_x \sum_{Q \ni x} |Q|\,\|h_Q\|$ is replaced by an arbitrary upper bound; the inequality is monotone in $\zeta_0$ and the maximum is an admissible value, so nothing is lost. The paper's lattice in $\mathbb{R}^D$ with qubits is generalized to any finite metric space of sites with a uniform local dimension $q$, and no bound $\|h_X\| \le 1$ is assumed. $\mathrm{dist}(X, Y)$ is `setDist X Y` ($0$ if either set is empty, in which case $A$ or $B$ is a scalar); $\ell$ is its natural-number floor, and $0^0 = 1$ at $t = 0$, $\ell = 0$. No disjointness of $X$ and $Y$ is assumed: $\ell \ge 1$ forces $X \cap Y = \emptyset$, and for $\ell = 0$ the bound is $2\|A\|\|B\||X|$. $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 27, Appendix C.4, display (48)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_48 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (X Y : Finset Λ) (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : LatticeHamSim.CommLR.SupportedOn X A) (hB : LatticeHamSim.CommLR.SupportedOn Y B) (t : ℝ) :
    ‖LatticeHamSim.CommLR.evolve (LatticeHamSim.CommLR.H h) t A * B - B * LatticeHamSim.CommLR.evolve (LatticeHamSim.CommLR.H h) t A‖ ≤
      2 * ‖A‖ * ‖B‖ * X.card * (2 * ζ₀ * |t|) ^ ⌊LatticeHamSim.CommLR.setDist X Y⌋₊ /
        (⌊LatticeHamSim.CommLR.setDist X Y⌋₊).factorial := by sorry

end LatticeHamSim.StrictLR
