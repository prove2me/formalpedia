-- Prove2me | Theorems.Thm_HiringLP_SimLower_theorem_3
-- name    : HiringLP.SimLower.theorem_3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:02:30.907137+00:00
-- url     : https://prove2.me/theorems/73ffc144-6fa8-4d9c-800c-76c24b8fa575
-- title:
--   Theorem 3 — on τ-bounded instances ALG^{s*}_sim earns ≥ α^τ_k LP_sim(I)
-- statement:
--   Let $\tau\in(0,1)$ and let $I=(k,n,p,v)$ be a valid Simultaneous Offering instance whose values all satisfy $v_i\ge\tau$. Let $(y,z)$ be any optimal solution of $\mathrm{LP}_{\mathrm{sim}}(I)$, and let $s^*\in[0,1]$ be a maximiser over $[0,1]$ of
--   $$s\ \longmapsto\ s-\frac{s}{\tau}+\frac{\mathbb E[\min\{\mathrm{Pois}(sk),k\}]}{\tau k}.$$
--   Then the algorithm $\mathrm{ALG}^{s^*}_{\mathrm{sim}}$ run on $y$ satisfies
--   $$R_{\mathrm{ALG}^{s^*}_{\mathrm{sim}}}(I)\ \ge\ \alpha^\tau_k\,\mathrm{LP}_{\mathrm{sim}}(I),\qquad \alpha^\tau_k=\sup_{0\le s\le1}\Big(s-\frac{s}{\tau}+\frac{\mathbb E[\min\{\mathrm{Pois}(sk),k\}]}{\tau k}\Big).$$
--
--   Since $\mathrm{LP}_{\mathrm{sim}}(I)\ge\mathrm{OPT}_{\mathrm{sim}}(I)$ (Lemma 10), a value-ordered policy is an $\alpha^\tau_k$-approximation on $\tau$-bounded instances, with $\alpha^\tau_k\to1$ as $k\to\infty$ for fixed $\tau$.
--
--   **Formalization Note** The paper's $s^*$ ("the optimal value" of $s$) is read as a maximiser of the $\alpha^\tau_k$ objective; one exists because the objective is continuous on $[0,1]$, and at it the objective equals $\alpha^\tau_k$. The theorem holds for every optimal LP solution, including ties $v_i=1$. Values are sorted (part of validity); $R$ is the exact expected reward with overage cost $1$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. 30, Theorem 3

import Mathlib
import Definitions.Def_HiringLP_SimLower_Model
import Definitions.Def_HiringLP_SimLower_LP
import Definitions.Def_HiringLP_SimLower_Algorithm
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimLower

/-- Theorem 3 (p. 30): for `τ ∈ (0,1)` and a τ-bounded instance, `ALG^{s*}_sim` run on an optimal LP
solution earns at least `α^τ_k · LP_sim(I)`, where `s*` is a maximiser of the `α^τ_k` objective over
`[0, 1]`. -/
theorem theorem_3 {n : ℕ} (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (I : SimInstance n) (hI : I.Valid)
    (hτ : I.TauBounded τ) (y : Fin n → ℝ) (z : ℝ) (hopt : IsLPOpt I y z)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1)
    (hsmax : ∀ s' ∈ Set.Icc (0 : ℝ) 1, ratioObj I.k τ s' ≤ ratioObj I.k τ s) :
    alpha I.k τ * LPsim I ≤ algReward I y s := by sorry

end HiringLP.SimLower
