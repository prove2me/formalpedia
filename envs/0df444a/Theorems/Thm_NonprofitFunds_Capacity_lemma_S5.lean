-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S5
-- name    : NonprofitFunds.Capacity.lemma_S5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:58.158023+00:00
-- url     : https://prove2.me/theorems/e9e754b9-b03a-46c4-a3fc-c427127e53fe
-- title:
--   Lemma S.5, pp. S7–S8 (PDF 36–37) — â(p1) solving (4) exists and is unique exactly on [p⁺_l, p⁺_u] when k1 ≤ k̄
-- statement:
--   Fix the data and an admissible capacity $k_1$. For a program level $p_1\in[0,\hat B_1]$, let $\hat a(p_1)$ be a discretionary administration level $a_1\in[0,\hat B_1-p_1]$ satisfying equation (4),
--   $$(r+1)\hat B_2(p_1,a_1)=k_1+\delta(a_1),$$
--   where $\hat B_2(p_1,a_1)=\hat B_2(p_1,a_1,\hat B_1-p_1-a_1)$. Let $\bar k$ be the capacity with $\bar k/(r+1)=\max_{p_1}\hat B_2(p_1,0)$.
--   1. (a) If $k_1>\bar k$, then $\hat a(p_1)$ does not exist for any $p_1\in[0,\hat B_1]$.
--   2. (b) If $k_1\le\bar k$, there are $p^+_l\le p^+_u$ with
--   $$\{p_1\in[0,\hat B_1]:(r+1)\hat B_2(p_1,0)\ge k_1\}=[p^+_l,p^+_u],$$
--   such that $\hat a(p_1)$ exists and is unique for $p_1\in[p^+_l,p^+_u]$ and does not exist for $p_1\in[0,\hat B_1]\setminus[p^+_l,p^+_u]$.
--
--   This lemma makes the "exhausted capacity" branch of problem (2) one-dimensional: along it, $a_1=\hat a(p_1)$ is a function of $p_1$ on $[p^+_l,p^+_u]$.
--
--   **Formalization Note.** "$k_1\le\bar k$" is stated as: some $p\in[0,\hat B_1]$ has $(r+1)\hat B_2(p,0)\ge k_1$; "$k_1>\bar k$" is its negation. The two are equivalent to the page's comparisons with $\bar k$ but do not require $\bar k$ to be a real number in the admissible range.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), pp. S7–S8 (PDF 36–37), Lemma S.5, constraint (S.2b) = equation (4)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.5, pp. S7–S8: existence and uniqueness of `â(p1)` solving (4).
(a) If `k1 > k̄`, no `p1 ∈ [0, B̂1]` admits a solution `a1 ∈ [0, B̂1 − p1]` of (4).
(b) If `k1 ≤ k̄`, there are `p⁺_l ≤ p⁺_u` with `{p1 : (r + 1) B̂2(p1, 0) ≥ k1} = [p⁺_l, p⁺_u]`
such that `â(p1)` exists and is unique for `p1 ∈ [p⁺_l, p⁺_u]` and does not exist otherwise. -/
theorem lemma_S5 (P : Params) (hP : P.Standing) (k1 : ℝ) (hk1 : P.Admissible k1) :
    (¬ P.BelowKbar k1 → ∀ p ∈ Set.Icc 0 (P.Bhat1 k1),
      ¬ ∃ a, 0 ≤ a ∧ a ≤ P.Bhat1 k1 - p ∧ P.Eq4 k1 p a) ∧
    (P.BelowKbar k1 → ∃ pl pu : ℝ, pl ≤ pu ∧ P.PlusSet k1 = Set.Icc pl pu ∧
      (∀ p ∈ Set.Icc pl pu, ∃! a, 0 ≤ a ∧ a ≤ P.Bhat1 k1 - p ∧ P.Eq4 k1 p a) ∧
      (∀ p ∈ Set.Icc 0 (P.Bhat1 k1), p ∉ Set.Icc pl pu →
        ¬ ∃ a, 0 ≤ a ∧ a ≤ P.Bhat1 k1 - p ∧ P.Eq4 k1 p a)) := by sorry

end NonprofitFunds.Capacity
