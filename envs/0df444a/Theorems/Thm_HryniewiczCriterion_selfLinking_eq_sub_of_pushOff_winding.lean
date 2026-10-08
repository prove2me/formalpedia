-- Prove2me | Theorems.Thm_HryniewiczCriterion_selfLinking_eq_sub_of_pushOff_winding
-- name    : HryniewiczCriterion.selfLinking_eq_sub_of_pushOff_winding
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-07T16:40:36.465651+00:00
-- url     : https://prove2.me/theorems/570aa145-c688-4cb9-bd52-a87c55781c00
-- title:
--   Twisting formula: the self-linking number equals the linking of any $\xi$-push-off minus its winding relative to the global frame
-- statement:
--   Let $S=H^{-1}(1)$ be strictly star-shaped and $P=(x,T)$ a prime periodic orbit. Let $V(s)=r(s)\big(\cos\theta(s)\,Z_1+\sin\theta(s)\,Z_2\big)$ at $x(Ts)$ be a smooth non-vanishing section of $\xi$ along $P$, where $r>0$ is $1$-periodic and
--   $$\theta(s+1)=\theta(s)+2\pi k,\qquad k\in\mathbb{Z},$$
--   so $V$ winds $k$ times relative to the global frame $(Z_1,Z_2)$, $\omega_0(Z_1,Z_2)=1$. If for all small $\varepsilon>0$ the push-off $s\mapsto (x(Ts)+\varepsilon V(s))/|\cdot|$ has linking number $m$ with $P$, then
--   $$\operatorname{sl}(P)=m-k .$$
--   Proof idea: rotating the push-off direction once positively in $\xi$ changes the push-off by a meridian of $P$, which adds $+1$ to the linking number. So $\mathrm{link}(P,P+\varepsilon V)=\mathrm{link}(P,P+\varepsilon Z_1)+k$; the homotopy $r_\tau=(1-\tau)r+\tau$, $\theta_\tau=(1-\tau)\theta+\tau\cdot 2\pi k s$ keeps the push-off disjoint from $P$. Checked numerically on a Hopf fibre of the round sphere ($k=0,\pm1,2$ give $\operatorname{sl}+k$ with $\operatorname{sl}=-1$).
-- source:
--   Twisting formula for framings of a transverse knot (Rolfsen, Knots and Links, 1976, Ch. 5D; Geiges, An Introduction to Contact Topology, 2008, §3.5.2); used in U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, Proposition 2.1 (cited for necessity in Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, outline after Theorem 1.8).

import Definitions.Def_HryniewiczCriterion_GlobalSection
import Definitions.Def_HryniewiczCriterion_SelfLinking

open HryniewiczCriterion
open scoped ContDiff

theorem HryniewiczCriterion.selfLinking_eq_sub_of_pushOff_winding (H : R4 → ℝ) (hS : IsStrictlyStarShapedLevel H) (P : PeriodicOrbit H) (hP : P.IsPrime)
    (r θ : ℝ → ℝ) (hr : ContDiff ℝ ∞ r) (hθ : ContDiff ℝ ∞ θ) (hr0 : ∀ s, 0 < r s)
    (hrper : ∀ s, r (s + 1) = r s) (k : ℤ) (hθper : ∀ s, θ (s + 1) = θ s + 2 * Real.pi * k)
    (m : ℤ)
    (hlink : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      IsLinkingNumber (orbitLoop P)
        (fun s => radialNormalize (P.x (P.T * s) + ε • (r s • (Real.cos (θ s) • xiFrame1 H (P.x (P.T * s)) + Real.sin (θ s) • xiFrame2 H (P.x (P.T * s)))))) m) :
    HasSelfLinkingNumber H P (m - k) := by sorry
