-- Prove2me | Theorems.Thm_InvariantEKF_error_flow_multiplicative
-- name    : InvariantEKF.error_flow_multiplicative
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T01:17:56.042293+00:00
-- url     : https://prove2.me/theorems/920a5f0c-95f4-4ae5-9530-f8479a7f2558
-- title:
--   Lemma 2: the flow of $\frac{d}{dt}\eta_t=g_{u_t}(\eta_t)$ is multiplicative
-- statement:
--   Let $G$ be a matrix Lie group and let $g_u$ satisfy $g_u(ab)=a\,g_u(b)+g_u(a)\,b$ for all inputs $u$ and $a,b\in G$. Assume that $(t,\eta)\mapsto g_{u_t}(\eta)$ is locally Lipschitz in $\eta$, uniformly for $t$ in compact windows, so that $\frac{d}{dt}\eta_t=g_{u_t}(\eta_t)$ has a well-defined flow $\Phi_t$. Then for all $\eta_0,\eta_0'\in G$ and $t\ge0$,
--
--   $$\Phi_t(\eta_0\eta_0')=\Phi_t(\eta_0)\,\Phi_t(\eta_0').$$
--
--   **Formalization Note** The flow is written through solutions. If $\eta,\eta'$ are solutions on $[0,\infty)$ with values in $G$ and $\zeta$ is a solution with $\zeta_0=\eta_0\eta'_0$, then $\zeta_t=\eta_t\eta'_t$ for all $t\ge0$. The Lipschitz condition is the standing assumption under which "the flow" exists.
-- source:
--   Barrau and Bonnabel, The invariant extended Kalman filter as a stable observer, arXiv:1410.1465v4 (2015), Appendix B, Lemma 2, eq. (57), p. 26

import Mathlib
import Definitions.Def_InvariantEKF_Basic

open MeasureTheory Matrix Filter Topology

namespace InvariantEKF

theorem error_flow_multiplicative {N : ℕ} {U : Type*} (G : Set (Matrix (Fin N) (Fin N) ℝ))
    (hG : IsMatrixLieGroup G) (g : U → Matrix (Fin N) (Fin N) ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hg : ∀ v, ∀ a ∈ G, ∀ b ∈ G, g v (a * b) = a * g v b + g v a * b)
    (u : ℝ → U) (hreg : IsLocLipschitzField (fun t => g (u t)))
    (η η' ζ : ℝ → Matrix (Fin N) (Fin N) ℝ)
    (hη : IsSolution (fun t => g (u t)) (Set.Ici 0) η) (hηG : ∀ t, 0 ≤ t → η t ∈ G)
    (hη' : IsSolution (fun t => g (u t)) (Set.Ici 0) η') (hη'G : ∀ t, 0 ≤ t → η' t ∈ G)
    (hζ : IsSolution (fun t => g (u t)) (Set.Ici 0) ζ) (h0 : ζ 0 = η 0 * η' 0) :
    ∀ t, 0 ≤ t → ζ t = η t * η' t := by sorry

end InvariantEKF
