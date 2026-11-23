-- Prove2me | Theorems.Thm_MPECRelax_ScholtesConv_Supplement_theorem_3_8
-- name    : MPECRelax.ScholtesConv.Supplement.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T11:33:35.984697+00:00
-- url     : https://prove2.me/theorems/e6f3a23d-905c-4551-81cb-955dbda389ee
-- title:
--   Theorem 3.8, p. 19 — MPEC-CPLD (MPEC-LICQ) implies CPLD (LICQ) for R^KDB(t) where I^00_Φ(x, t) = ∅
-- statement:
--   Let $x^*$ be a feasible point of the MPEC (1), with continuously differentiable data.
--
--   1. If MPEC-CPLD holds at $x^*$, there are $\bar t>0$ and a neighborhood $N$ of $x^*$ such that, for all $t\in(0,\bar t]$, every $x\in N\cap X^{KDB}(t)$ with $I^{00}_\Phi(x,t)=\emptyset$ satisfies standard CPLD for $R^{KDB}(t)$.
--   2. If MPEC-LICQ holds at $x^*$, there are $\bar t>0$ and a neighborhood $N$ of $x^*$ such that, for all $t\in(0,\bar t]$, every $x\in N\cap X^{KDB}(t)$ with $I^{00}_\Phi(x,t)=\emptyset$ satisfies standard LICQ for $R^{KDB}(t)$.
--
--   In both parts $N$ does not depend on $t$. Away from the corner points $G_i(x)=H_i(x)=t$, the relaxed programs inherit the stronger constraint qualification from the MPEC.
--
--   **Formalization Note** The two readings of the parenthesized statement are stated as a conjunction of two implications, each with its own $\bar t$ and $N$.
--
--   Differences from the source:
--   - encoding: f, g_i, h_i, G_i, H_i are at least continuously differentiable (standing assumption, p. 1) → the hypothesis hP : P.IsC1 (every datum is ContDiff ℝ 1), so `gradient` is the true gradient; reason: the paper states the assumption once for the whole paper; it is carried explicitly, with the same instances
--   - encoding: ℝⁿ, indices i = 1, …, m (p, l), ∇g_i(x)ᵀd, a neighborhood N of x* → EuclideanSpace ℝ (Fin n), 0-based Fin indices, the inner product ⟪∇g_i(x), d⟫, N ∈ 𝓝 x*; reason: Lean conventions; same instances
--   - reading: one sentence with the parenthetical variant "MPEC-CPLD (MPEC-LICQ) … CPLD (LICQ)" and one t̄, N → a conjunction of two implications, MPEC-CPLD ⇒ CPLD and MPEC-LICQ ⇒ LICQ, each with its own t̄ and N; reason: the parenthesis names a second version of the theorem; taking the smaller t̄ and the intersection of the neighborhoods turns either form into the other
-- source:
--   Hoheisel, Kanzow, Schwartz, Theoretical and numerical comparison of relaxation methods for mathematical programs with complementarity constraints, Preprint 299, Univ. Würzburg, Sept. 2010, p. 19, Theorem 3.8 (proof pp. 19–20)

import Mathlib
import Definitions.Def_MPECRelax_ScholtesConv_NLP
import Definitions.Def_MPECRelax_ScholtesConv_MPEC
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_CQ
import Definitions.Def_MPECRelax_ScholtesConv_Supplement_KDB

open Filter Topology Set

namespace MPECRelax.ScholtesConv.Supplement

theorem theorem_3_8 {n m p l : ℕ} (P : MPEC n m p l) (hP : P.IsC1) (xs : E n)
    (hxs : P.Feasible xs) :
    (MPEC_CPLD P xs → ∃ tbar : ℝ, 0 < tbar ∧ ∃ N ∈ 𝓝 xs, ∀ t ∈ Ioc 0 tbar, ∀ x ∈ N,
        (RKDB P t).Feasible x → I00Phi P x t = ∅ → IsCPLD (RKDB P t) x) ∧
    (MPEC_LICQ P xs → ∃ tbar : ℝ, 0 < tbar ∧ ∃ N ∈ 𝓝 xs, ∀ t ∈ Ioc 0 tbar, ∀ x ∈ N,
        (RKDB P t).Feasible x → I00Phi P x t = ∅ → IsLICQ (RKDB P t) x) := by sorry

end MPECRelax.ScholtesConv.Supplement
