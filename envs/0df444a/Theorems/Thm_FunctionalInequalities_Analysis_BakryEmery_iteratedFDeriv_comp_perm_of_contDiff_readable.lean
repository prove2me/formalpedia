-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_perm_of_contDiff_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:05.082706+00:00
-- url     : https://prove2.me/theorems/62e73549-6b73-43c8-a852-062236b36219
-- title:
--   Full Permutation Symmetry of Iterated Derivatives
-- statement:
--   This is the full permutation-symmetry theorem for iterated Fréchet derivatives of a smooth map.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. For every $n\in\mathbb N$, $x\in E$, every list of directions $v:\operatorname{Fin}(n)\to E$, and every permutation $\sigma$ of $\operatorname{Fin}(n)$,
--
--   $$D^nf(x)[v\circ\sigma]=D^nf(x)[v].$$
--
--   This provides the higher-order symmetry used when rearranging derivative slots in multilinear and cumulant expansions.
--
--   **Formalization Note.** The smoothness assumption is `ContDiff ℝ ∞`; the statement includes the case $n=0$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_comp_perm_of_contDiff {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
--       (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
--       iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IteratedDerivative`](https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7).
--
--   Supporting theorems: [`iteratedFDeriv_comp_swap_zero_one`](https://prove2.me/theorems/b0248a78-8f38-49b0-948c-7fe54558fabb), [`iteratedFDeriv_succ_comp_perm_of_fix_zero`](https://prove2.me/theorems/cc6ef6bd-ffe5-427d-b172-1c1aebc1558a).
--
--   Previous: [`iteratedFDeriv_comp_swap_zero_one`](https://prove2.me/theorems/b0248a78-8f38-49b0-948c-7fe54558fabb).
--
--   [Source excerpt, lines 250–252](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L250-L252) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L246-L353 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_perm_of_contDiff_readable {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin n → E) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by sorry
