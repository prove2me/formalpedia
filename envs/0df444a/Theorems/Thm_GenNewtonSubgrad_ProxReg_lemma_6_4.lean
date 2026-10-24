-- Prove2me | Theorems.Thm_GenNewtonSubgrad_ProxReg_lemma_6_4
-- name    : GenNewtonSubgrad.ProxReg.lemma_6_4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:55.380328+00:00
-- url     : https://prove2.me/theorems/7e53622d-b3cf-4a03-b562-b996aaedb6e7
-- title:
--   Lemma 6.4, p. 27 (corrected range) — $(v^*,x^*)\in\mathrm{gph}\,D^*\nabla e_\lambda\varphi(x,v)\iff(v^*-\lambda x^*,x^*)\in\mathrm{gph}\,\partial^2\varphi(x-\lambda v,v)$
-- statement:
--   Let $\varphi:\mathbb R^n\to(-\infty,\infty]$ be proper and prox-bounded, and continuously prox-regular at $\bar x$ for $\bar v\in\partial\varphi(\bar x)$ with modulus $r>0$ (radius $\varepsilon$). Then there is $\lambda_0$ with $0<\lambda_0\le r^{-1}$ such that for every $\lambda\in(0,\lambda_0)$ there is a neighbourhood $W$ of $\bar x+\lambda\bar v$ on which $e_\lambda\varphi$ is differentiable and, for every $x\in W$, with $v=\nabla e_\lambda\varphi(x)$,
--   $$x^*\in(D^*\nabla e_\lambda\varphi)(x,v)(v^*)\iff x^*\in\partial^2\varphi(x-\lambda v,v)(v^*-\lambda x^*)\qquad\text{for all }v^*,x^*\in\mathbb R^n.$$
--
--   In the paper's notation, $(v^*,x^*)\in\operatorname{gph}(D^*\nabla e_\lambda\varphi)(x,v)\iff(v^*-\lambda x^*,x^*)\in\operatorname{gph}\partial^2\varphi(x-\lambda v,v)$. This transfers second-order information between $\varphi$ and its envelope, and is used to transfer (H1)–(H2) in Theorem 6.6.
--
--   **Correction.** Lemma 6.4 is stated "in the setting of Lemma 6.3, for any $\lambda\in(0,r^{-1})$, $x\in U_\lambda$"; it inherits the parameter-range defect of Lemma 6.3 (see Lemma 6.3(ii)) and is posed for $\lambda$ sufficiently small, on a neighbourhood of $\bar x+\lambda\bar v$.
--
--   **Formalization Note.** $(v^*,x^*)\in\operatorname{gph}D^*G(x,v)$ is read as $x^*\in D^*G(x,v)(v^*)$, the convention of Definition 5.1 and of the proof. $\nabla e_\lambda\varphi$ is the gradient of the real-valued envelope.
-- source:
--   Khanh, Mordukhovich & Phat, A Generalized Newton Method for Subgradient Systems, arXiv:2009.10551v2, p. 27, Lemma 6.4 (corrected parameter range; see Formalization Note)

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_GenNewtonSubgrad_ProxReg_VarAnalysis
import Definitions.Def_GenNewtonSubgrad_ProxReg_Envelope
open Filter Topology

namespace GenNewtonSubgrad.ProxReg

theorem lemma_6_4 {n : ℕ} (φ : EuclideanSpace ℝ (Fin n) → EReal)
    (xbar vbar : EuclideanSpace ℝ (Fin n)) (r ε : ℝ)
    (hproper : IsProperFn φ) (hbdd : IsProxBounded φ)
    (hreg : IsContProxRegularAt φ xbar vbar r ε) :
    ∃ lam₀ : ℝ, 0 < lam₀ ∧ lam₀ ≤ r⁻¹ ∧ ∀ lam : ℝ, 0 < lam → lam < lam₀ →
      ∃ W ∈ 𝓝 (xbar + lam • vbar),
        (∀ x ∈ W, DifferentiableAt ℝ (fun z => (moreauEnv φ lam z).toReal) x) ∧
        ∀ x ∈ W, ∀ v' x' : EuclideanSpace ℝ (Fin n),
          x' ∈ coderiv (sv (gradient (fun z => (moreauEnv φ lam z).toReal))) x
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) v' ↔
            x' ∈ secondSubdiff φ (x - lam • gradient (fun z => (moreauEnv φ lam z).toReal) x)
              (gradient (fun z => (moreauEnv φ lam z).toReal) x) (v' - lam • x') := by sorry

end GenNewtonSubgrad.ProxReg
