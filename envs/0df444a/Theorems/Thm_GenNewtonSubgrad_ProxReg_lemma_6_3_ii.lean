-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_3_ii
-- name    : GenNewtonSubgrad.ProxReg.lemma_6_3_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:36:06.014982+00:00
-- url     : https://prove2.me/theorems/3e3a54d8-f5bf-4eb9-90bd-de3752f67209
-- title:
--   Lemma 6.3(ii), p. 27 (corrected range) — $\mathrm{Prox}_\lambda\varphi$ is single-valued, monotone, Lipschitz near $\bar x+\lambda\bar v$ and maps $\bar x+\lambda\bar v$ to $\bar x$
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and continuously prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ (radius $\varepsilon$). Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every $\lambda\in(0,\lambda_0)$ there are a neighbourhood $W$ of $\bar x+\lambda\bar v$ and a map $P:\mathbb R^n\to\mathbb R^n$ with
--
--   1. $\operatorname{Prox}_\lambda\varphi(x)=\{P(x)\}$ for all $x\in W$ (single-valued);
--   2. $\langle P(x)-P(y),x-y\rangle\ge0$ for all $x,y\in W$ (monotone);
--   3. $P$ is Lipschitz continuous on $W$;
--   4. $\operatorname{Prox}_\lambda\varphi(\bar x+\lambda\bar v)=\{\bar x\}$.
--
--   **Correction.** As printed, (ii) is claimed for every $\lambda\in(0,r^{-1})$ on all of $U_\lambda$. For $\varphi(y)=\tfrac12y^2$ on $[-5,5]$, $-1000-|y-10|$ on $[9,11]$, $+\infty$ elsewhere ($\bar x=\bar v=0$, $r=1$, $\lambda=\tfrac12$), $\operatorname{Prox}_\lambda\varphi(0)=\{9\}\neq\{0\}$. The statement is posed as Poliquin–Rockafellar [53, Theorem 4.4] gives it: for $\lambda$ sufficiently small, on a neighbourhood.
--
--   **Formalization Note.** The paper writes both $P_\lambda\varphi$ and $\operatorname{Prox}_\lambda\varphi$ for the same map. $\operatorname{Prox}_\lambda\varphi$ is the argmin set; single-valuedness is part of the conclusion.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 27, Lemma 6.3(ii) (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.ProxReg

theorem lemma_6_3_ii {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar),
        ∃ p : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n),
          (∀ x ∈ W, prox φ lam x = {p x}) ∧
          (∀ x ∈ W, ∀ y ∈ W, 0 ≤ ⟪p x - p y, x - y⟫_ℝ) ∧
          (∃ L, LipschitzOnWith L p W) ∧
          prox φ lam (xbar + lam • vbar) = {xbar} := by sorry

end GenNewtonSubgrad.ProxReg
