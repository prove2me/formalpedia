-- Prove2me | Theorems.Thm_MPECRelax_ScholtesMFCQ_theorem_3_2
-- name    : MPECRelax.ScholtesMFCQ.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:49.864985+00:00
-- url     : https://prove2.me/theorems/dbe58481-3bc5-42fe-bca9-a7a6e26e5527
-- title:
--   Theorem 3.2 — MPEC-MFCQ implies standard MFCQ for Scholtes' relaxed programs near x*
-- statement:
--   Let the data $f,g_i,h_i,G_i,H_i$ of the MPEC (1) be continuously differentiable, let $x^*$ be feasible for (1), and suppose MPEC-MFCQ holds at $x^*$. Then there exist a neighbourhood $N$ of $x^*$ and $\bar t>0$ such that, for every $t>0$, standard MFCQ for Scholtes' relaxed program
--   $$R^S(t):\quad \min f(x)\ \text{ s.t. }\ g_i(x)\le0,\ h_j(x)=0,\ G_i(x)\ge0,\ H_i(x)\ge0,\ G_i(x)H_i(x)\le t$$
--   is satisfied at all $x\in N\cap X^S(t)$, where $X^S(t)$ is the feasible set of $R^S(t)$.
--
--   The theorem guarantees that KKT multipliers exist at local minimizers of the relaxed programs near $x^*$, which is the hypothesis of the convergence result for the method (Theorem 3.1).
--
--   **Formalization Note.** The paper introduces $\bar t>0$ but never uses it: $t$ is free in the statement, and the proof works for every $t>0$ (the relaxed program is defined for $t>0$, p. 8). We keep $\bar t$ to mirror the statement and quantify over all $t>0$; the neighbourhood $N$ is chosen before $t$ and does not depend on it. "Standard MFCQ for $R^S(t)$" is MFCQ of the NLP $R^S(t)$ at $x$, with its own active set, including $-G_i\le0$, $-H_i\le0$ and the product constraint $G_iH_i-t\le0$ when active. The C¹ standing assumption of p. 1 is the hypothesis `IsC1`.
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 11, Theorem 3.2

import Mathlib
import Definitions.Def_MPECRelax_ScholtesMFCQ_Basic

open Filter Topology
open scoped RealInnerProductSpace

namespace MPECRelax.ScholtesMFCQ

/-- Theorem 3.2 (p. 11): if `xs` is feasible for the MPEC (1) and MPEC-MFCQ holds at
`xs`, there are a neighbourhood `N` of `xs` and `t̄ > 0` such that standard MFCQ for
the relaxed program R^S(t) holds at every `x ∈ N ∩ X^S(t)`. The paper's statement never
uses `t̄`; the parameter `t > 0` is free, as in its proof, and `N` does not depend on `t`. -/
theorem theorem_3_2 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1)
    (xs : MPECRelax.ScholtesConv.E n) (hfeas : P.Feasible xs) (hCQ : P.MPEC_MFCQ xs) :
    ∃ N ∈ 𝓝 xs, ∃ tbar : ℝ, 0 < tbar ∧
      ∀ t : ℝ, 0 < t → ∀ x ∈ N, (P.RS t).Feasible x → (P.RS t).IsMFCQ x := by sorry

end MPECRelax.ScholtesMFCQ
