-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_convexOn_potential_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:22.352427+00:00
-- url     : https://prove2.me/theorems/8bd14eff-e39b-41f3-a887-8c1cbe3d5c1e
-- title:
--   Convexity of the Finite-Copy Suspension Potential
-- statement:
--   This auxiliary convexity statement formalizes the convexity component of Proposition 7.1, p. 28, equations (109)–(110), of Bizeul–Klartag–Lehec (arXiv:2610.05474v1).
--
--   Let $E$ be a real inner product space and let $V,f:E\to\mathbb R$ be $C^2$. Let $a,M,\beta,\sigma\in\mathbb R$ and $N\in\mathbb N$. Assume:
--   1. $\beta\ge0$.
--   2. $D^2V(x)[v,v]\ge a\|v\|^2$ for every $x,v\in E$, with the bilinear second derivative represented by `bilinearIteratedFDerivTwo`.
--   3. $\|D(Df)(x)\|\le M$ for every $x\in E$, using `fderiv` and its operator norm.
--   4. $(\beta/\sqrt N)M\le a$.
--
--   The function defined by `potential`,
--   $$
--   W_N(s,x)=\sum_{i\in\operatorname{Fin}N}V(x_i)+\beta\left|\sigma s-\frac{\sum_i f(x_i)}{\sqrt N}\right|,
--   $$
--   is convex on all of $\mathbb R\times(\operatorname{Fin}N\to E)$.
--
--   This isolates the deterministic convexity condition used in the suspension construction, rather than the full proposition.
--
--   **Formalization Note** No positivity restriction on $N$, $a$, $M$, or $\sigma$ is added. In particular $N=0$ is allowed, with Lean's totalized real division.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convexOn_potential {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
--       {a M beta sigma : ℝ} (hbeta : 0 ≤ beta)
--       (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
--       (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
--       (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
--       ConvexOn ℝ Set.univ (potential V f beta sigma N)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Basic`](https://prove2.me/theorems/aaa7527c-3ccd-45dd-876d-0915bc183526).
--
--   Supporting theorems: [`convexOn_of_hessian_ge`](https://prove2.me/theorems/dc198aa0-40e7-4ce6-bf96-9622594c954d).
--
--   Next: [`exists_copies`](https://prove2.me/theorems/5967f3b2-764f-4fd4-8e97-8cae228211c5).
--
--   [Source excerpt, lines 85–90](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L85-L90) · Frozen source `408915f`.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Proposition 7.1, p. 28. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Basic.lean#L83-L104 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Basic`, declaration `FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Basic

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.KLS.LogConcave.Suspension.convexOn_potential_readable {V f : E → ℝ} (hV : ContDiff ℝ 2 V) (hf : ContDiff ℝ 2 f)
    {a M beta sigma : ℝ} (hbeta : 0 ≤ beta)
    (hVlower : ∀ x v, a * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ V x v v)
    (hfbound : ∀ x, ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ M)
    (N : ℕ) (hN : beta / Real.sqrt N * M ≤ a) :
    ConvexOn ℝ Set.univ (potential V f beta sigma N) := by sorry
