-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_neg_add_comp_gradient_readable
-- name    : FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:23.650126+00:00
-- url     : https://prove2.me/theorems/e0b4ed2f-da69-4e68-a1df-7fa0bdfaa735
-- title:
--   Lipschitz Monge–Ampère Exponent
-- statement:
--   This is a regularity lemma for the Monge–Ampère exponent.
--
--   Let $u,V:\mathbb R^n\to\mathbb R$. Assume that $u$ is globally Lipschitz with constant $L$, $\nabla u$ is globally Lipschitz with constant $G$, and $V\in C^1$. Then there exists $L_F\in[0,\infty)$ such that
--
--   $$x\longmapsto -u(x)+V(\nabla u(x))$$
--
--   is globally $L_F$-Lipschitz. The result is dimension-finite but applies to every $n\in\mathbb N$ and supplies the exponent regularity used by later weak Monge–Ampère identities.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_lipschitzWith_neg_add_comp_gradient {n : ℕ}
--       {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
--       (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
--       (hV : ContDiff ℝ 1 V) :
--       ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Lipschitz/Gradient`](https://prove2.me/theorems/c121ae0a-019e-498c-bab1-b5d194574dc8).
--
--   [Source excerpt, lines 12–16](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean#L12-L16) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean#L11-L31 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Lipschitz.Gradient`, declaration `FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Lipschitz_Gradient

theorem FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_readable {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x)) := by sorry
