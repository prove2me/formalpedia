-- Prove2me | Theorems.Thm_MMDarkPool_Exchange_remark_4_2
-- name    : MMDarkPool.Exchange.remark_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:36.930058+00:00
-- url     : https://prove2.me/theorems/148378a8-24e7-4c1b-ba30-606c7e48e22e
-- title:
--   Remark 4.2, p. 14 — the supremum over z^S̃ in (4.16) is attained at z^S̃ = −γq/(γ + η)
-- statement:
--   Fix the parameters of the lit/dark market-making model under its standing assumptions, any selection $\mathcal L^\star$ of market-maker volumes, an inventory $q\in\{-\bar q,\dots,\bar q\}$, a row $w=v(t,\cdot)$ with $w(q)<0$, and jump incentives $z=(z^{i,j,k})$. Let $\mathcal U(z^{\tilde S},z)$ denote the function $\mathcal U(z,q,\mathcal L^\star(z,q),w)$ of (4.16). Then the maximization over the price-risk incentive $z^{\tilde S}\in\mathbb R$ is explicit: for every $z^{\tilde S}\neq-\frac{\gamma}{\gamma+\eta}q$,
--   $$\mathcal U\big(z^{\tilde S},z\big)<\mathcal U\Big(-\frac{\gamma}{\gamma+\eta}\,q,\ z\Big).$$
--   So $z^{\tilde S}=-\frac{\gamma}{\gamma+\eta}q$ is the unique maximizer of $\mathcal U$ in $z^{\tilde S}$ for fixed $z$.
--
--   This removes one variable from the supremum defining the exchange's Hamiltonian $\mathcal H$, leaving a supremum over the jump incentives alone.
--
--   **Formalization Note.** The remark is stated in the paper without a sign condition. The $z^{\tilde S}$-dependent part of $\mathcal U$ is $w(q)$ times a strictly convex quadratic in $z^{\tilde S}$, so the supremum is attained at the stated point exactly when $w(q)<0$ (for $w(q)>0$ it is $+\infty$, for $w(q)=0$ every $z^{\tilde S}$ maximizes). The hypothesis $w(q)<0$ is therefore added; it holds for the negative value functions of the paper's setting. No best-response property of $\mathcal L^\star$ is needed, since $\mathcal L^\star$ depends on the jump incentives only.
-- source:
--   Baldacci, Manziuk, Mastrolia & Rosenbaum, arXiv:1912.01129v1, p. 14, Remark 4.2 (with 𝓤 of (4.16), p. 14)

import Mathlib
import Definitions.Def_MMDarkPool_Exchange_Model

namespace MMDarkPool.Exchange

theorem remark_4_2 (P : Params) (hP : Standing P) (Lstar : Inc P → ℤ → Vol) (q : ℤ) (hq : q ∈ Grid P) (w : ℤ → ℝ) (hw : w q < 0) (z : Inc P) (zS : ℝ) (hzS : zS ≠ -(P.γ / (P.γ + P.η)) * (q : ℝ)) : Ucal P Lstar (zS, z) q w < Ucal P Lstar (-(P.γ / (P.γ + P.η)) * (q : ℝ), z) q w := by sorry

end MMDarkPool.Exchange
