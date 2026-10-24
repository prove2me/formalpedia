-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_lipschitzWith_neg_add_comp_gradient_408915f
-- name    : FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:17:58.820857+00:00
-- url     : https://prove2.me/theorems/4b65bb4a-426b-4703-811d-eddd8099abb1
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
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Lipschitz/Gradient.lean#L11-L31 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Lipschitz.Gradient`, declaration `FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.PiL2

noncomputable section
open Set Metric
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.exists_lipschitzWith_neg_add_comp_gradient_408915f {n : ℕ}
    {u V : EuclideanSpace ℝ (Fin n) → ℝ} {L G : NNReal}
    (hL : LipschitzWith L u) (hG : LipschitzWith G (gradient u))
    (hV : ContDiff ℝ 1 V) :
    ∃ LF : NNReal, LipschitzWith LF (fun x => -u x + V (gradient u x)) := by sorry
