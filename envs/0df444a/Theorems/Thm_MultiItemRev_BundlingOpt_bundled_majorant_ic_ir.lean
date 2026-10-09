-- Prove2me | Theorems.Thm_MultiItemRev_BundlingOpt_bundled_majorant_ic_ir
-- name    : MultiItemRev.BundlingOpt.bundled_majorant_ic_ir
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:25:51.129294+00:00
-- url     : https://prove2.me/theorems/68a65b04-7be1-4481-a135-10dc38f7663c
-- title:
--   Proof of Theorem 16, p. 46 — µ̂ is feasible, IC and IR on [a, ∞)², and bundled
-- statement:
--   Let $\mu = (q,s)$ be an admissible symmetric two-good mechanism with buyer payoff $b$, let $a \ge 0$, and let $\hat\mu = (\hat q, \hat s)$ be its bundled majorant: with $t = y + z - a$,
--   $$\hat q(y,z) = \bigl(q_1(t,a), q_1(t,a)\bigr), \qquad \hat s(y,z) = \hat q(y,z)\cdot(y,z) - b(t,a).$$
--   Then:
--   1. $\hat q(y,z) \in [0,1]^2$ for all $(y,z)$;
--   2. $\hat\mu$ is incentive compatible on the quadrant $[a,\infty)^2$: $\hat q(\tilde x)\cdot x - \hat s(\tilde x) \le \hat b(x)$ for all $x, \tilde x \in [a,\infty)^2$;
--   3. $\hat\mu$ is individually rational on the quadrant: $\hat b(x) \ge 0$ for $x \in [a,\infty)^2$;
--   4. $\hat\mu$ is bundled: $\hat q(y,z)$ and $\hat s(y,z)$ depend on $(y,z)$ only through $y + z$.
--
--   Together these say that $\hat\mu$ is a bundled IC and IR mechanism on the support of two i.i.d. goods with values in $[a,\infty)$.
--
--   **Formalization Note** IC and IR are stated on the quadrant $[a,\infty)^2$, where the paper defines $\hat\mu$. A mechanism that is IC and IR on a domain containing the values of $X$ extends to all of $\mathbb{R}^2_+$ (p. 14, citing Hart and Reny 2015a, Appendix A.1); that extension is not part of this statement.
-- source:
--   Hart and Nisan, Approximate Revenue Maximization with Multiple Items, arXiv:1204.1846v3, p. 46, proof of Theorem 16 (q̂, ŝ subgradient; µ̂ IC and IR by Proposition 5; µ̂ bundled)

import Mathlib
import Definitions.Def_MultiItemRev_BundlingOpt_Model
import Definitions.Def_MultiItemRev_BundlingOpt_Bundling
open MeasureTheory
open scoped NNReal ENNReal

namespace MultiItemRev.BundlingOpt

theorem bundled_majorant_ic_ir (M : Mechanism (Fin 2)) (hM : IsAdmissible M)
    (hsym : IsSymmetric M) (a : ℝ≥0) :
    IsFeasible (bundledMajorant M a) ∧
      (∀ x x' : Fin 2 → ℝ≥0, (∀ i, a ≤ x i) → (∀ i, a ≤ x' i) →
        ∑ i, (bundledMajorant M a).q x' i * (x i : ℝ) - (bundledMajorant M a).s x' ≤
          buyerPayoff (bundledMajorant M a) x) ∧
      (∀ x : Fin 2 → ℝ≥0, (∀ i, a ≤ x i) → 0 ≤ buyerPayoff (bundledMajorant M a) x) ∧
      (∀ x x' : Fin 2 → ℝ≥0, x 0 + x 1 = x' 0 + x' 1 →
        (bundledMajorant M a).q x = (bundledMajorant M a).q x' ∧
          (bundledMajorant M a).s x = (bundledMajorant M a).s x') := by sorry

end MultiItemRev.BundlingOpt
