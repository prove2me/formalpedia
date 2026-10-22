-- Prove2me | Theorems.Thm_JobShopLTAS_Core_eq1_choice_of_alpha
-- name    : JobShopLTAS.Core.eq1_choice_of_alpha
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T07:57:57.123947+00:00
-- url     : https://prove2.me/theorems/57b66672-60cb-4035-b992-4a63e9d463b6
-- title:
--   Section 2.1, Eq. (1) — $\alpha=\varepsilon^k$ can be chosen so that the small jobs have total length at most $\varepsilon P_{\max}$
-- statement:
--   Let $m\ge 2$, $\mu\ge 1$, $0<\varepsilon<1$ and $P_{\max}>0$. For $\alpha_k=\varepsilon^k$ let $S_k=\{J_j\mid \alpha_k\varepsilon P_{\max}<l_j<\alpha_k P_{\max}\}$ be the small jobs with respect to $\alpha_k$. Then there is an integer $k$ with $1\le k\le\lceil m/\varepsilon\rceil$ such that
--   $$\sum_{J_j\in S_k} l_j\le\varepsilon P_{\max}.\tag{1}$$
--   The paper then sets $\alpha=\alpha_k$, which lies in $[\varepsilon^{\lceil m/\varepsilon\rceil},\varepsilon]$.
--
--   **Formalization Note.** The paper writes "$k\le m/\varepsilon$". The range $1\le k\le\lceil m/\varepsilon\rceil$ is the one for which $\alpha_k\in[\varepsilon^{\lceil m/\varepsilon\rceil},\varepsilon]$ as required at the start of Section 2.1: $k=0$ would give $\alpha=1>\varepsilon$, and $\lfloor m/\varepsilon\rfloor$ disjoint sets need not suffice. The hypothesis $\varepsilon<1$ is implicit in the paper (for $\varepsilon\ge 1$ the sets $B,S,T$ do not partition the jobs).
-- source:
--   Jansen, Solis-Oba, Sviridenko, Makespan Minimization in Job Shops: A Linear Time Approximation Scheme, SIAM J. Discrete Math. 16 (2003), p. 291, Section 2.1, Eq. (1)

import Mathlib
import Definitions.Def_JobShopLTAS_Core_Instance
import Definitions.Def_JobShopLTAS_Core_RestrictedProblem

namespace JobShopLTAS.Core

/-- §2.1, Eq. (1), p. 291: for `α_k = ε^k` with some `k ∈ {1, …, ⌈m/ε⌉}`, the small jobs
`S_k = {J_j | α_k ε P_max < l_j < α_k P_max}` have total length at most `ε P_max`. The paper
writes `k ≤ m/ε`; the index range `1 ≤ k ≤ ⌈m/ε⌉` is the one for which `α_k` lies in
`[ε^⌈m/ε⌉, ε]`. -/
theorem eq1_choice_of_alpha {m n : ℕ} (inst : Instance m n) (ε : ℝ)
    (hm : 2 ≤ m) (hμ : 1 ≤ inst.maxOps) (hε : 0 < ε) (hε1 : ε < 1) (hP : 0 < inst.Pmax) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ ⌈(m : ℝ) / ε⌉₊ ∧
      ∑ j ∈ inst.smallJobs ε (ε ^ k), inst.jobLength j ≤ ε * inst.Pmax := by sorry

end JobShopLTAS.Core
