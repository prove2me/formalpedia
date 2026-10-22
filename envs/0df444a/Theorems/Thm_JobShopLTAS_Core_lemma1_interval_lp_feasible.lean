-- Prove2me | Theorems.Thm_JobShopLTAS_Core_lemma1_interval_lp_feasible
-- name    : JobShopLTAS.Core.lemma1_interval_lp_feasible
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T08:49:29.917985+00:00
-- url     : https://prove2.me/theorems/6de801ef-1071-4885-a287-c33f025f3742
-- title:
--   Lemma 1 — for $C=\widetilde C^*_{\max}$ the interval LP (3)–(5) is feasible for some restricted schedule of the big operations
-- statement:
--   Let $m\ge 2$, $\mu\ge 1$, $0<\varepsilon<1$, $\varepsilon^{\lceil m/\varepsilon\rceil}\le\alpha\le\varepsilon$ and $P_{\max}>0$, and let $\widetilde C^*_{\max}$ be the optimum makespan of the restricted problem on the jobs $B\cup T$. Then there is a feasible restricted schedule $\sigma$ of the big operations (a feasible schedule of the big jobs in which every big operation starts at the beginning of an interval of the first type) such that, with $a_{|A|+1}=C=\widetilde C^*_{\max}$,
--   $$a_{|A|}\le \widetilde C^*_{\max}\le(1+\mu m\varepsilon)mP_{\max}\quad\text{and the linear program (3)–(5) has a feasible solution } (x_{jK}).$$
--   Here $A$ is the set of start and completion times of the big operations under $\sigma$, and the linear program asks for $x_{jK}\ge0$ ($J_j\in T$, $K$ a nondecreasing tuple in $\{0,\dots,|A|\}^{\mu_j}$) with $\sum_K x_{jK}=1$ for each tiny job and, on each machine $M_t$ and each interval $[a_k,a_{k+1})$ of the second type, total assigned tiny processing time at most $\Delta_{tk}$.
--
--   This is the statement that justifies the paper's algorithm: searching over the constantly many restricted big-operation schedules and solving the interval LP loses nothing relative to the restricted optimum.
--
--   **Formalization Note.** The range condition $C\in[a_{|A|},(1+\mu m\varepsilon)mP_{\max}]$ is where the paper defines the LP, and is part of `LPFeasible`. $\widetilde C^*_{\max}$ is an infimum; the paper's proof starts from "an optimum schedule $S^*$", so that the infimum is attained is part of what must be proved, not a hypothesis. $\varepsilon<1$ and $P_{\max}>0$ are implicit in the paper.
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 292, Section 2.2, Lemma 1

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem
import Definitions.Def_JobShopLTAS_Core_IntervalLP

namespace JobShopLTAS.Core

/-- Lemma 1 (§2.2, p. 292): for `C = C̃*_max`, the linear program (3)–(5) has a feasible
solution for some feasible restricted schedule `σ` of the big operations. -/
theorem lemma1_interval_lp_feasible {m n : ℕ} (inst : Instance m n) (ε α : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1)
    (hα_lo : ε ^ ⌈(m : ℝ) / ε⌉₊ ≤ α) (hα_hi : α ≤ ε) (hP : 0 < inst.Pmax) :
    ∃ σ : inst.Op → ℝ, inst.IsBigSchedule ε α σ ∧
      inst.LPFeasible ε α σ (inst.restrictedOpt ε α) := by sorry

end JobShopLTAS.Core
