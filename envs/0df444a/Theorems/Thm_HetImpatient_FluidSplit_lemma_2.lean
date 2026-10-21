-- Prove2me | Theorems.Thm_HetImpatient_FluidSplit_lemma_2
-- name    : HetImpatient.FluidSplit.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:34:55.420842+00:00
-- url     : https://prove2.me/theorems/2aa65903-0e62-41b6-b452-284b2a7111c4
-- title:
--   Lemma 2 (first sentence), p. 1071 — the class cost function C_i is nonincreasing and convex
-- statement:
--   Let $C_i(n)$ be the value of the within-class program (6) of class $i$ at capacity $n$:
--   $$C_i(n) = \inf\Big\{\sum_{j=1}^{J} \lambda_{j}\,\bar c_i(w_{j}) \;:\; J\ge 1,\ \lambda_j, n_j \ge 0,\ \sum_j \lambda_j = \Lambda_i,\ \lambda_j\,\bar F_i(w_j) \le n_j\,\mu_i,\ \sum_j n_j \le n\Big\}.$$
--   Under the standing assumptions of the model ($\Lambda_i>0$, $\mu_i>0$, $\bar F_i$ a survival function with $\bar F_i(\infty)=0$) and with nonnegative costs $\bar c_i \ge 0$, the function $C_i$ is nonincreasing and convex on $[0,\infty)$:
--   $$0 \le n \le n' \implies C_i(n') \le C_i(n),\qquad C_i\big(\theta n + (1-\theta) n'\big) \le \theta\, C_i(n) + (1-\theta)\, C_i(n') \quad (n,n'\ge 0,\ \theta\in[0,1]).$$
--
--   This is the first sentence of the paper's Lemma 2. Convexity of every $C_i$ makes the across-class program (2) a convex resource-allocation problem, which the paper uses to read the optimality conditions of Proposition 2 as sufficient.
--
--   **Formalization Note.** $C_i$ is a real infimum. On $[0,\infty)$ the feasible set is nonempty (one never-served subclass with $w=\infty$ and no capacity) and, with $\bar c_i\ge 0$, the costs are bounded below by $0$; this is why the statement is posed on $[0,\infty)$ and carries the hypothesis $\bar c_i \ge 0$, which the paper's cost functions (abandonment and queue-length costs) satisfy. The second sentence of Lemma 2 (differentiability of $C_i$ for $n < \Lambda_i/\mu_i$) is not part of this statement: it needs regularity of $F_i$ and of the cost that the paper does not state and fails for a general $\bar c_i$.
-- source:
--   Bassamboo, Randhawa & Wu, Optimally scheduling heterogeneous impatient customers, Manufacturing & Service Operations Management 25(3):1066–1080 (2023), p. 1071, Lemma 2 (first sentence)

import Mathlib
import Definitions.Def_HetImpatient_FluidSplit_Model

namespace HetImpatient.FluidSplit

theorem lemma_2 {m : ℕ} (D : ClassData m) (hD : D.Standing) (hc : D.CostNonneg) (i : Fin m) :
    AntitoneOn (C D i) (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) (C D i) := by sorry

end HetImpatient.FluidSplit
