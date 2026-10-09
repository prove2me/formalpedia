-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_lemma_5
-- name    : LatticeHamSim.StrictLR.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:45.306287+00:00
-- url     : https://prove2.me/theorems/425e7772-83de-4449-b8f4-dfc577189942
-- title:
--   Lemma 5 (4), p. 9 = (49), p. 27 — ‖O_X(t;H) − O_X(t;H_Ω)‖ ≤ |X|‖O_X‖(2ζ₀|t|)^ℓ/ℓ!, ℓ = ⌊dist(X,Λ∖Ω)⌋, for dist(X,Λ∖Ω) ≥ 1
-- statement:
--   Let $\Lambda$ be a finite metric space of sites, each carrying $\mathbb{C}^q$, and let $H = \sum_{X \subseteq \Lambda} h_X$, where every $h_X$ is Hermitian and supported on $X$. Assume **strict locality**, $h_X = 0$ whenever $\mathrm{diam}(X) > 1$, and let $\zeta_0$ satisfy $\sum_{Q \ni x} |Q|\,\|h_Q\| \le \zeta_0$ for every site $x$. For $\Omega \subseteq \Lambda$ let $H_\Omega = \sum_{Z \subseteq \Omega} h_Z$. Let $O_X$ be an operator supported on $X$, assume that every site of $X$ is at distance at least $1$ from every site outside $\Omega$, and put $\ell = \lfloor \mathrm{dist}(X, \Lambda \setminus \Omega) \rfloor$. Then for every real $t$,
--   $$\big\| (U_t^{H})^\dagger O_X U_t^{H} - (U_t^{H_\Omega})^\dagger O_X U_t^{H_\Omega} \big\| \le |X|\, \|O_X\|\, \frac{(2\zeta_0 |t|)^{\ell}}{\ell!},$$
--   where $U_t^{J} = e^{-iJt}$, so that $(U_t^J)^\dagger O U_t^J = e^{iJt} O e^{-iJt}$.
--
--   This is the form of the Lieb–Robinson bound the paper's algorithm uses: the Heisenberg evolution of a local operator under the full Hamiltonian is approximated by the evolution under the terms inside a region $\Omega$ around its support, with an error that decays superexponentially in the distance from the support to the outside of $\Omega$.
--
--   **Formalization Note** The hypothesis $\mathrm{dist}(x, y) \ge 1$ for $x \in X$, $y \notin \Omega$ is an addition to the paper's statement, and it is necessary: as printed, (4) fails when $\ell = 0$. Take two qubits $x, y$ at distance $1/2$, $H = J\,\sigma^x_x \sigma^x_y$, $\Omega = \{x\}$ (so $H_\Omega = 0$) and $O_X = \sigma^z_x$; then $\ell = 0$ and the right side is $1$, while the left side is $2|\sin Jt|$, which reaches $2$. The added hypothesis gives $\ell \ge 1$ whenever $\Omega \neq \Lambda$, implies $X \subseteq \Omega$ (which the paper's proof assumes), and is vacuous when $\Omega = \Lambda$. The paper's $\zeta_0$ (a maximum) is replaced by an arbitrary upper bound, the lattice by a finite metric space with uniform local dimension $q$; no bound $\|h_X\| \le 1$ is assumed. $\mathrm{dist}(X, \Lambda \setminus \Omega)$ is `setDist` ($0$ if a set is empty). $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 9, Lemma 5, display (4); restated as display (49), p. 27, Appendix C.4

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem lemma_5 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (Ω X : Finset Λ) (O : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (hO : LatticeHamSim.CommLR.SupportedOn X O)
    (hfar : ∀ x ∈ X, ∀ y : Λ, y ∉ Ω → 1 ≤ dist x y) (t : ℝ) :
    ‖LatticeHamSim.CommLR.evolve (LatticeHamSim.CommLR.H h) t O - LatticeHamSim.CommLR.evolve (HOmega h Ω) t O‖ ≤
      X.card * ‖O‖ * (2 * ζ₀ * |t|) ^ ⌊LatticeHamSim.CommLR.setDist X (Finset.univ \ Ω)⌋₊ /
        (⌊LatticeHamSim.CommLR.setDist X (Finset.univ \ Ω)⌋₊).factorial := by sorry

end LatticeHamSim.StrictLR
