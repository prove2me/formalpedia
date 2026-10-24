-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_iii
-- name    : GenNewtonSubgrad.ProxReg.lemma_6_3_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:54.266469+00:00
-- url     : https://prove2.me/theorems/d4c60c3e-8139-41d4-8b10-4d654edc017c
-- title:
--   Lemma 6.3(iii), p. 27 (corrected range) — $\nabla e_\lambda\varphi(x)=\lambda^{-1}(x-\mathrm{Prox}_\lambda\varphi(x))=(\lambda I+\partial\varphi^{-1})^{-1}(x)$ near $\bar x+\lambda\bar v$
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and continuously prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ (radius $\varepsilon$). Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every $\lambda\in(0,\lambda_0)$ there are neighbourhoods $W$ of $\bar x+\lambda\bar v$ and $V$ of $\bar v$ with the following properties.
--
--   1. For every $x\in W$, $\operatorname{Prox}_\lambda\varphi(x)\neq\emptyset$ and, for every $p\in\operatorname{Prox}_\lambda\varphi(x)$, the real function $e_\lambda\varphi$ has gradient
--   $$\nabla e_\lambda\varphi(x)=\frac1\lambda\big(x-p\big)\quad\text{at }x.\qquad(6.7)$$
--   2. For every $x\in W$, the localized resolvent is the gradient:
--   $$\{v\in V : v\in\partial\varphi(x-\lambda v)\}=\{\nabla e_\lambda\varphi(x)\}.$$
--   Since $(\lambda I+\partial\varphi^{-1})^{-1}(x)=\{v : v\in\partial\varphi(x-\lambda v)\}$, this is the second equality of (6.7) for the localization of $\partial\varphi$ to $V$.
--
--   **Correction.** As printed, (6.7) is claimed for every $\lambda\in(0,r^{-1})$ on all of $U_\lambda$, with the global $(\lambda I+\partial\varphi^{-1})^{-1}$. Both fail in general: in the example $\varphi(y)=\tfrac12y^2$ on $[-5,5]$, $-1000-|y-10|$ on $[9,11]$, $+\infty$ elsewhere, with $\lambda=\tfrac12$ and $x=0$, the set $\{v : v\in\partial\varphi(-v/2)\}$ contains both $0$ and $-18$. The statement is posed in the form of Poliquin–Rockafellar [53, Theorem 4.4], the source the paper cites: $\lambda$ sufficiently small, a neighbourhood of $\bar x+\lambda\bar v$, and the localization $V$ of $\partial\varphi$ around $\bar v$.
--
--   **Formalization Note.** The gradient identity is stated with `HasGradientAt`, so differentiability of $e_\lambda\varphi$ at $x$ is asserted, not presupposed. $\partial$ is the analytic limiting subdifferential (agreeing with (2.9) for $\varphi$ l.s.c. around $\bar x$).
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 27, Lemma 6.3(iii), (6.7) (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem lemma_6_3_iii {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar), ∃ V ∈ 𝓝 vbar,
        (∀ x ∈ W, (prox φ lam x).Nonempty ∧ ∀ p ∈ prox φ lam x,
          HasGradientAt (fun z => (moreauEnv φ lam z).toReal) (lam⁻¹ • (x - p)) x) ∧
        (∀ x ∈ W, {v | v ∈ V ∧ v ∈ NonconvexSplitting.Shared.LimitingSubdiff φ (x - lam • v)} =
          {gradient (fun z => (moreauEnv φ lam z).toReal) x}) := by sorry

end GenNewtonSubgrad.ProxReg
