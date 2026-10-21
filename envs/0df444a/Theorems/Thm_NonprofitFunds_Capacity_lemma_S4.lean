-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S4
-- name    : NonprofitFunds.Capacity.lemma_S4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:51:57.769891+00:00
-- url     : https://prove2.me/theorems/356dac39-98bd-4b5c-a69f-3985e1b23371
-- title:
--   Lemma S.4, pp. S6–S7 (PDF 35–36) — the optimum p*_nb of problem (S.1), case by case around k̄
-- statement:
--   Fix the data and an admissible capacity $k_1$. Problem (S.1) maximizes $J_{nb}(p_1)$ over $p_1\in[0,\hat B_1]$ subject to
--   $$\text{(S.1a) } (r+1)p_1\le\theta,\qquad \text{(S.1b) } \hat B_2(p_1,0)\ge 0,\qquad \text{(S.1c) } (r+1)\hat B_2(p_1,0)\le k_1 .$$
--   Let $\tilde p_{nb}\in[0,\hat B_1]$ maximize $J_{nb}$ on $[0,\hat B_1]$, and let $p^0_u$ be such that $\{p\in[0,\hat B_1]:\hat B_2(p,0)\ge 0\}=[0,p^0_u]$. Let $p^*_{nb}$ be any optimal solution of (S.1).
--   1. (a) If $(r+1)\hat B_2(p,0)\le k_1$ for every $p\in[0,\hat B_1]$ (that is, $k_1\ge\bar k$), then $p^*_{nb}=\min(\tilde p_{nb},\theta/(r+1),p^0_u)$.
--   2. (b) Suppose $(r+1)\hat B_2(p,0)>k_1$ for some $p$ (that is, $k_1<\bar k$), and $\{p\in[0,\hat B_1]:(r+1)\hat B_2(p,0)\ge k_1\}=[p^+_l,p^+_u]$.
--      - (i) If $p^+_u\le\theta/(r+1)$, then $p^*_{nb}=\min\big(\max(p^+_u,\tilde p_{nb}),\theta/(r+1),p^0_u\big)$.
--      - (ii) If $p^+_u>\theta/(r+1)$ and $p^+_l>0$, then $p^*_{nb}=\min(p^+_l,\theta/(r+1))$.
--      - (iii) If $p^+_u>\theta/(r+1)$ and $(r+1)\hat B_2(0,0)>k_1$ (so that $p^+_l=0$ and $p^+_l$ is not a root), then (S.1) has no feasible solution.
--
--   Together with Lemma S.2 this solves the "unused capacity" branch of problem (2); it is the appendix form of Proposition 4.
--
--   **Formalization Note.** Here $\hat B_2(p,0)$ means $\hat B_2(p,0,\hat B_1-p)$. The page's threshold $\bar k$ is replaced by the equivalent conditions on $k_1$ stated in (a) and (b). The page's case (iii) reads "$p^+_l=0$"; it is stated under the strict condition $(r+1)\hat B_2(0,0)>k_1$, because when $(r+1)\hat B_2(0,0)=k_1$ exactly, $p_1=0$ is feasible and "no feasible solution" fails.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), pp. S6–S7 (PDF 35–36), Lemma S.4, problem (S.1)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.4, pp. S6–S7: the optimal solution `p*_nb` of problem (S.1), in terms of a maximizer
`p̃_nb` of `J_nb` on `[0, B̂1]`, the right root `p⁰_u` of `B̂2(·, 0)`, and
`[p⁺_l, p⁺_u] = {p1 : (r + 1) B̂2(p1, 0) ≥ k1}`. -/
theorem lemma_S4 (P : Params) (hP : P.Standing) (k1 : ℝ) (hk1 : P.Admissible k1)
    (pnb p0u : ℝ) (hnb_mem : pnb ∈ Set.Icc 0 (P.Bhat1 k1))
    (hnb : IsMaxOn (P.Jnb k1) (Set.Icc 0 (P.Bhat1 k1)) pnb)
    (hZ : P.ZeroSet k1 = Set.Icc 0 p0u) :
    -- (a) k1 ≥ k̄
    ((∀ q ∈ Set.Icc 0 (P.Bhat1 k1), (P.r + 1) * P.Bhat2 k1 q 0 (P.Bhat1 k1 - q) ≤ k1) →
      ∀ p, P.IsOptimalS1 k1 p → p = min pnb (min (P.theta k1 / (P.r + 1)) p0u)) ∧
    -- (b) k1 < k̄
    (∀ pl pu : ℝ, P.PlusSet k1 = Set.Icc pl pu →
      (∃ q ∈ Set.Icc 0 (P.Bhat1 k1), k1 < (P.r + 1) * P.Bhat2 k1 q 0 (P.Bhat1 k1 - q)) →
      -- (i)
      (pu ≤ P.theta k1 / (P.r + 1) → ∀ p, P.IsOptimalS1 k1 p →
        p = min (max pu pnb) (min (P.theta k1 / (P.r + 1)) p0u)) ∧
      -- (ii)
      (P.theta k1 / (P.r + 1) < pu → 0 < pl → ∀ p, P.IsOptimalS1 k1 p →
        p = min pl (P.theta k1 / (P.r + 1))) ∧
      -- (iii), with "p⁺_l = 0" read as: no left root, (r + 1) B̂2(0, 0) > k1
      (P.theta k1 / (P.r + 1) < pu → k1 < (P.r + 1) * P.Bhat2 k1 0 0 (P.Bhat1 k1) →
        ∀ p, ¬ P.FeasibleS1 k1 p)) := by sorry

end NonprofitFunds.Capacity
