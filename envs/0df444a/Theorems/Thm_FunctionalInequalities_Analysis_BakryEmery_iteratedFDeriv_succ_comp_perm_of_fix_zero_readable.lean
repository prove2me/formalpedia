-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_succ_comp_perm_of_fix_zero_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:57.282922+00:00
-- url     : https://prove2.me/theorems/cc6ef6bd-ffe5-427d-b172-1c1aebc1558a
-- title:
--   Higher-Derivative Symmetry Under Permutations Fixing One Index
-- statement:
--   This is a technical symmetry lemma for iterated Fréchet derivatives.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. Fix $n\in\mathbb N$ and assume that the $n$-th derivative is invariant under every permutation of its $n$ input directions. Then, for every $x\in E$, every $v:\operatorname{Fin}(n+1)\to E$, and every permutation $\sigma$ of $\operatorname{Fin}(n+1)$ satisfying $\sigma(0)=0$,
--
--   $$D^{n+1}f(x)[v\circ\sigma]=D^{n+1}f(x)[v].$$
--
--   The statement supplies the stabilizer-of-the-first-index step in the permutation symmetry of higher derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_succ_comp_perm_of_fix_zero {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
--       (ih : ∀ (y : E) (w : Fin n → E) (τ : Equiv.Perm (Fin n)),
--         iteratedFDeriv ℝ n f y (w ∘ τ) = iteratedFDeriv ℝ n f y w)
--       (x : E) (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
--       iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (n + 1) f x v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IteratedDerivative`](https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7).
--
--   Previous: [`iteratedFDeriv_inner_self_apply`](https://prove2.me/theorems/93b102a6-8056-49d9-b513-0807baf24636) · Next: [`iteratedFDeriv_comp_swap_zero_one`](https://prove2.me/theorems/b0248a78-8f38-49b0-948c-7fe54558fabb).
--
--   [Source excerpt, lines 126–130](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L126-L130) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L124-L193 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_succ_comp_perm_of_fix_zero_readable {f : E → F} (hf : ContDiff ℝ ∞ f) {n : ℕ}
    (ih : ∀ (y : E) (w : Fin n → E) (τ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℝ n f y (w ∘ τ) = iteratedFDeriv ℝ n f y w)
    (x : E) (v : Fin (n + 1) → E) (σ : Equiv.Perm (Fin (n + 1))) (hσ : σ 0 = 0) :
    iteratedFDeriv ℝ (n + 1) f x (v ∘ σ) = iteratedFDeriv ℝ (n + 1) f x v := by sorry
