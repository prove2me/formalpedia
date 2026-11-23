-- Prove2me | Theorems.Thm_LogBarrierIPM_Iterations_Supplement_theorem_15
-- name    : LogBarrierIPM.Iterations.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T17:17:40.685349+00:00
-- url     : https://prove2.me/theorems/029fe199-2497-4125-8db7-9163503e3601
-- title:
--   Theorem 15 — the general tropical barycenter characterization
-- statement:
--   Assume Assumption 13: the Puiseux primal-dual feasible set has a point with all coordinates strictly positive. For every positive Puiseux series $\boldsymbol\mu$, system (17) has a unique solution $\mathcal C(\boldsymbol\mu)$, and
--   $$\operatorname{val}\bigl(\mathcal C(\boldsymbol\mu)\bigr)=\max\{z\in\operatorname{val}(\mathcal F):\operatorname{tgap}(z)\le\operatorname{val}(\boldsymbol\mu)\}.$$
--   Here maximum means membership and domination of every point. At every real level $\lambda$, the computed real vector $C^{\rm trop}(\lambda)$ is this greatest point after tropical embedding. Thus the default in its definition is unreachable on the theorem’s domain. The parameter ranges over all positive series, not only monomials. This characterizes the general tropical central path.
--
--   Differences from the source:
--   - encoding: relations over the ordered field K → eventual relations between evaluations of the published convergent series; reason: p. 7 identifies order and equality with eventual evaluations; no domain is restricted
--   - encoding: the named unique solution C(μ) and the quantity (18) → explicit unique existence plus the greatest-point property, also at every real level; reason: the existence claim on p. 14 and the definition on p. 16 are made explicit to avoid conditional or default-value vacuity
-- source:
--   Allamigeon, Benchimol, Gaubert, Joswig, Log-Barrier Interior Point Methods Are Not Strongly Polynomial, arXiv:1708.01544v2, p. 15, Theorem 15

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_Supplement_TropicalLP

open Filter Matrix

namespace LogBarrierIPM.Iterations.Supplement
open LogBarrierIPM.Curvature

theorem theorem_15 {m n : ℕ} (A : Matrix (Fin m) (Fin n) Puiseux)
    (b : Fin m → Puiseux) (c : Fin n → Puiseux)
    (hstrict : StrictlyFeasibleK A b c)
    (μ : Puiseux) (hμ : KPositive μ) :
    (∃! z : PuiseuxSlackPoint n m, IsCentralK A b c μ z) ∧
    (∀ z : PuiseuxSlackPoint n m, IsCentralK A b c μ z →
      IsGreatest (tropicalSublevel A b c μ.val) (valPoint z)) ∧
    (∀ lam : ℝ, IsGreatest (tropicalSublevel A b c (lam : WithBot ℝ))
      (tropicalizeReal (tropicalPath A b c lam))) := by sorry

end LogBarrierIPM.Iterations.Supplement
