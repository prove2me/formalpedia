-- Prove2me | Theorems.Thm_MMDarkPool_Exchange_theorem_3
-- name    : MMDarkPool.Exchange.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:50.736625+00:00
-- url     : https://prove2.me/theorems/84d6e298-81bf-4d68-b44a-a94bc8823919
-- title:
--   Theorem 3, p. 14 — the exchange's HJB equation (4.15) has a unique continuous viscosity solution
-- statement:
--   Consider the lit/dark market-making model under its standing assumptions: horizon $T>0$, tick $\mathcal T>0$, $\sigma,\gamma,\eta,\epsilon>0$, $A^j,\theta^j,c^j>0$, $\Gamma^l\ge\Gamma^d>0$, risk limit $\bar q\in\mathbb N$ and finite volume sets $\mathcal V^l,\mathcal V^d\subset\mathbb N$ containing $0$. Let $\mathcal L^\star(z,q)$ be any best response of the market maker in the sense of (4.6): for each inventory $q\in\{-\bar q,\dots,\bar q\}$ and jump incentives $z$, an admissible volume vector maximizing the market maker's Hamiltonian $h(\cdot,z,q)$ of (4.10). Consider the exchange's HJB equation
--   $$\begin{cases}0=\partial_tv(t,q)+\mathcal H\big(q,\mathcal L^\star,v(t,\cdot)\big), & q\in\{-\bar q,\dots,\bar q\},\ t\in[0,T),\\ v(T,q)=-1,\end{cases}\qquad\qquad(4.15)$$
--   where $\mathcal H(q,\mathcal L^\star,v(t,\cdot))=\sup_{z\in\mathbb R^{2(\#\mathcal V^l+\#\mathcal V^d)+1}}\mathcal U(z,q,\mathcal L^\star(z,q),v(t,\cdot))$ is the exchange's Hamiltonian (4.16).
--
--   Then (4.15) has a continuous viscosity solution $v$ on $[0,T]\times\{-\bar q,\dots,\bar q\}$, and it is unique: every continuous viscosity solution $w$ of (4.15) agrees with $v$ on $[0,T]\times\{-\bar q,\dots,\bar q\}$.
--
--   This is the well-posedness half of the paper's main theorem. Through the ansatz (4.14), the solution $v$ is the reduced value function of the exchange's make-take fees design problem, and the supremum in (4.15) gives the exchange's optimal incentives.
--
--   **Formalization Note.** Only the first sentence of Theorem 3 is formalized; the identity $v^E_0=v(0,Q_0)=v^E(0,\tilde S_0,\bar N_0,N_0,Y_0)$ and the statement that the optimal incentives solve the supremum need the stochastic control model and are not part of this statement. The paper solves (4.15) "for a specific optimal response"; here the statement holds for every best-response selection. The readings used: $\bar q\in\mathbb N$ for "$2\bar q\in\mathbb N$"; admissible volumes keep the inventory within the risk limits $\pm\bar q$ (§5.1.1); $0\in\mathcal V^l,\mathcal V^d$; one sum per pool in (4.10); $\mathcal H$ is valued in the extended reals; and the viscosity notion is the standard per-component one for a finite system of backward ODEs ($C^1$ test functions in $t$, interior test times $t_0\in(0,T)$, nonlocal argument $v(t_0,\cdot)$, subsolution $\partial_t\varphi+\mathcal H\ge0$ at local maxima of $v(\cdot,q)-\varphi$, supersolution $\le0$ at local minima), with continuity on $[0,T]$ and the terminal condition as separate requirements. Values of $v$ off the grid are not constrained and do not enter $\mathcal H$ with a nonzero coefficient. The informal "impacts small with respect to the tick" and "$\epsilon$ small enough" are not assumed.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, p. 14, Theorem 3 (first assertion), with (4.15) p. 13 and (4.16) p. 14

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Model

namespace MMDarkPool.Exchange

theorem theorem_3 (P : Params) (hP : Standing P) (Lstar : Inc P → ℤ → Vol) (hL : IsBestResponse P Lstar) : ∃ v : ℝ → ℤ → ℝ, IsViscositySolution P Lstar v ∧ ∀ w : ℝ → ℤ → ℝ, IsViscositySolution P Lstar w → ∀ t ∈ Set.Icc 0 P.T, ∀ q ∈ Grid P, w t q = v t q := by sorry

end MMDarkPool.Exchange
