-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_comp_swap_zero_one_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:01:57.799476+00:00
-- url     : https://prove2.me/theorems/b0248a78-8f38-49b0-948c-7fe54558fabb
-- title:
--   Swap Symmetry of Higher Derivatives
-- statement:
--   This is a pointwise Schwarz-type symmetry statement for iterated Fréchet derivatives.
--
--   Let $E$ be a real inner-product space, let $F$ be a real normed space, and let $f:E\to F$ be $C^\infty$. For every $n\in\mathbb N$, $x\in E$, and $v:\operatorname{Fin}(n+2)\to E$, swapping the first two derivative directions leaves the $(n+2)$-nd iterated derivative unchanged:
--
--   $$D^{n+2}f(x)[v\circ(0\ 1)]=D^{n+2}f(x)[v].$$
--
--   Here $(0\ 1)$ is the permutation exchanging the indices $0$ and $1$.
--
--   The lemma is a technical component for establishing full permutation symmetry of higher derivatives.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_comp_swap_zero_one {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
--       (v : Fin (n + 2) → E) :
--       iteratedFDeriv ℝ (n + 2) f x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (n + 2) f x v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IteratedDerivative`](https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7).
--
--   Previous: [`iteratedFDeriv_succ_comp_perm_of_fix_zero`](https://prove2.me/theorems/cc6ef6bd-ffe5-427d-b172-1c1aebc1558a) · Next: [`iteratedFDeriv_comp_perm_of_contDiff`](https://prove2.me/theorems/62e73549-6b73-43c8-a852-062236b36219).
--
--   [Source excerpt, lines 222–224](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L222-L224) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L220-L244 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_comp_swap_zero_one_readable {f : E → F} (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E)
    (v : Fin (n + 2) → E) :
    iteratedFDeriv ℝ (n + 2) f x (v ∘ Equiv.swap 0 1) = iteratedFDeriv ℝ (n + 2) f x v := by sorry
