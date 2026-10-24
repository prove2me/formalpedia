-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_remark_6_5
-- name    : GenNewtonSubgrad.ProxReg.remark_6_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:53.93483+00:00
-- url     : https://prove2.me/theorems/c7e8189a-f99e-48ab-98c8-68f695a8609d
-- title:
--   Remark 6.5, p. 27 (corrected range) — Algorithm 6.2 is Algorithm 5.3 applied to $e_\lambda\varphi$
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and continuously prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ (radius $\varepsilon$). Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every $\lambda\in(0,\lambda_0)$ there is a neighbourhood $W$ of $\bar x+\lambda\bar v$ such that for every $x\in W$, $\operatorname{Prox}_\lambda\varphi(x)\neq\emptyset$, and for every $p\in\operatorname{Prox}_\lambda\varphi(x)$, with $v=\lambda^{-1}(x-p)$ as in (6.4):
--
--   1. $v=\nabla e_\lambda\varphi(x)$ (the envelope has gradient $v$ at $x$);
--   2. for every $d$, the Newton inclusion (6.5) is the Newton inclusion of $e_\lambda\varphi$:
--   $$-v\in\partial^2\varphi(x-\lambda v,v)(\lambda v+d)\iff-\nabla e_\lambda\varphi(x)\in\partial^2e_\lambda\varphi(x)(d);$$
--   3. for every $d$, $\partial^2e_\lambda\varphi(x)(d)=\partial\langle d,\nabla e_\lambda\varphi\rangle(x)$ as sets, so in particular $-\nabla e_\lambda\varphi(x)\in\partial^2e_\lambda\varphi(x)(d)\iff-\nabla e_\lambda\varphi(x)\in\partial\langle d,\nabla e_\lambda\varphi\rangle(x)$.
--
--   Consequently, near $\bar x+\lambda\bar v$ a step of Algorithm 6.2 is a step of Algorithm 5.3 for $e_\lambda\varphi$.
--
--   **Correction.** The remark rests on Lemmas 6.3 and 6.4 for $\lambda\in(0,r^{-1})$ on $U_\lambda$, which fail as printed (see Lemma 6.3(ii)); it is posed for $\lambda$ sufficiently small, on a neighbourhood of $\bar x+\lambda\bar v$.
--
--   **Formalization Note.** The item formalizes the displayed equivalences of the remark; its last sentence ("Algorithm 6.2 reduces to Algorithm 5.3") is their consequence. $\partial^2e_\lambda\varphi(x)(d)$ is the coderivative of the single-valued map $\nabla e_\lambda\varphi$ at $(x,\nabla e_\lambda\varphi(x))$, and $\partial\langle d,\nabla e_\lambda\varphi\rangle$ is the analytic limiting subdifferential of a real function continuous near $x$.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 27, Remark 6.5 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
open Filter Topology
open scoped InnerProductSpace

namespace GenNewtonSubgrad.ProxReg

theorem remark_6_5 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar), ∀ x ∈ W, (prox φ lam x).Nonempty ∧ ∀ p ∈ prox φ lam x,
        HasGradientAt (fun z => (moreauEnv φ lam z).toReal) (lam⁻¹ • (x - p)) x ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          -(lam⁻¹ • (x - p)) ∈ secondSubdiff φ (x - lam • (lam⁻¹ • (x - p))) (lam⁻¹ • (x - p))
              (lam • (lam⁻¹ • (x - p)) + d) ↔
            -gradient (fun z => (moreauEnv φ lam z).toReal) x ∈
              coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
                (gradient (fun z => (moreauEnv φ lam z).toReal) x) d) ∧
        (∀ d : EuclideanSpace ℝ (Fin n),
          coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) d =
            NonconvexSplitting.Shared.LimitingSubdiff
              (fun z => ((⟪d, gradient (fun w => (moreauEnv φ lam w).toReal) z⟫_ℝ : ℝ) : EReal)) x)
          := by sorry

end GenNewtonSubgrad.ProxReg
