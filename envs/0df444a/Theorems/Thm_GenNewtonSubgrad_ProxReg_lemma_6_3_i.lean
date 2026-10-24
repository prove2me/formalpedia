-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_i
-- name    : GenNewtonSubgrad.ProxReg.lemma_6_3_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:57.776626+00:00
-- url     : https://prove2.me/theorems/f4981b22-136d-449f-bbee-411f1d2dcba5
-- title:
--   Lemma 6.3(i), p. 27 (corrected range) — the Moreau envelope is finite and $C^{1,1}$ near $\bar x+\lambda\bar v$, a neighbourhood inside $U_\lambda$
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and continuously prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ (and radius $\varepsilon>0$ in (4.1)). Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every $\lambda\in(0,\lambda_0)$ there is a neighbourhood $W$ of $\bar x+\lambda\bar v$ with
--
--   1. $W\subseteq U_\lambda=\operatorname{rge}(I+\lambda\partial\varphi)$;
--   2. $e_\lambda\varphi$ is finite on $W$;
--   3. $e_\lambda\varphi$ is of class $C^{1,1}$ on $W$: differentiable at every point of $W$, with $\nabla e_\lambda\varphi$ Lipschitz on $W$.
--
--   This is the smoothness of the envelope on which the reduction of Algorithm 6.2 to Algorithm 5.3 rests.
--
--   **Correction.** As printed, Lemma 6.3 claims this for every $\lambda\in(0,r^{-1})$ on all of $U_\lambda$. That is false, because prox-regularity is a property of $\varphi$ near $\bar x$ while $\operatorname{Prox}_\lambda\varphi$ minimizes over all of $\mathbb R^n$: for $\varphi(y)=\tfrac12y^2$ on $[-5,5]$, $-1000-|y-10|$ on $[9,11]$, $+\infty$ elsewhere, $\bar x=\bar v=0$, $r=1$, $\lambda=\tfrac12$, one gets $\operatorname{Prox}_\lambda\varphi(x)=\{9\}$ near $0$. The cited source, Poliquin–Rockafellar [53, Theorem 4.4], gives the conclusions for $\lambda$ sufficiently small and on a neighbourhood; that is the form stated here. The quantifier order is $\exists\lambda_0\in(0,r^{-1}]\ \forall\lambda\in(0,\lambda_0)\ \exists W$.
--
--   **Formalization Note.** Only the first sentence of (i) is formalized. Its second sentence ("$\bar x$ solves (1.5) iff $\nabla e_\lambda\varphi(\bar x)=0$") compares $\bar x$ with a neighbourhood of $\bar x+\lambda\bar v$ and is meaningful only for $\bar v=0$, where it follows from (ii) and (iii); for $\bar v\neq0$ it is false as printed (on $\mathbb R$, $\varphi(y)=y$ for $y\ge0$ and $-|y|^{3/2}$ for $y<0$ is continuously prox-regular at $0$ for $\bar v=1$ and $0\in\partial\varphi(0)$, but $0\notin\operatorname{Prox}_\lambda\varphi(0)$ for every $\lambda>0$, so $\nabla e_\lambda\varphi(0)\neq0$); the convex clause ($U_\lambda=\mathbb R^n$ for convex $\varphi$) is not used and not stated. $\partial$ is the analytic limiting subdifferential, which agrees with (2.9) for $\varphi$ l.s.c. around $\bar x$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 27, Lemma 6.3(i) (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem lemma_6_3_i {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar), W ⊆ rgeShift φ lam ∧
        (∀ x ∈ W, moreauEnv φ lam x ≠ ⊤ ∧ moreauEnv φ lam x ≠ ⊥) ∧
        (∀ x ∈ W, DifferentiableAt ℝ (fun z => (moreauEnv φ lam z).toReal) x) ∧
        ∃ L, LipschitzOnWith L (gradient (fun z => (moreauEnv φ lam z).toReal)) W := by sorry

end GenNewtonSubgrad.ProxReg
