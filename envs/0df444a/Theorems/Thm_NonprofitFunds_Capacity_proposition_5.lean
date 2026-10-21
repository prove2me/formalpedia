-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_proposition_5
-- name    : NonprofitFunds.Capacity.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:13.373461+00:00
-- url     : https://prove2.me/theorems/b3fa47e6-cf2f-42e5-8bab-9b3aaa7fb98a
-- title:
--   Proposition 5, pp. 17–18 (PDF 17–18) — optimal program spending among allocations that exhaust second-period capacity
-- statement:
--   Fix the data. Restrict problem (2) to the allocations that exhaust second-period capacity, i.e. whose $a_1$ and $p_1$ satisfy equation (4), $(r+1)\hat B_2(p_1,a_1)=k_1+\delta(a_1)$. For an admissible $k_1\le\bar k$, let $[p^+_l,p^+_u]=\{p\in[0,\hat B_1]:(r+1)\hat B_2(p,0)\ge k_1\}$.
--   1. A feasible allocation of (2) satisfying (4) exists if and only if
--   $$p^+_l\le\frac{\theta}{r+1}.$$
--   2. There is a threshold $\underline k$ such that, whenever $p^+_l\le\theta/(r+1)$, $\hat a$ solves (4) on $[p^+_l,p^+_u]$ as in Lemma S.5, and $p^*_b$ is the program spending of an allocation that is optimal among the feasible allocations satisfying (4):
--      - (a) if $k_1\le\underline k$, then $p^*_b=\min(\tilde p_b,\theta/(r+1))$ for every maximizer $\tilde p_b$ of $J_b$ on $[p^+_l,p^+_u]$;
--      - (b) if $k_1>\underline k$, then $p^*_b=\min(p^+_u,\theta/(r+1))$.
--
--   Proposition 5 solves the "exhausted capacity" branch of problem (2); Proposition 1 follows by comparing it with the "unused capacity" branch (Lemma S.4).
--
--   **Formalization Note.** The page defines $p^+_l$ only for $k_1\le\bar k$, so this hypothesis is added. $\tilde p_b$ is any maximizer of $J_b$ over $[p^+_l,p^+_u]$ (at $k_1=\underline k$ it is $p^+_u$). The threshold $\underline k$ is existentially quantified here, independently of Lemma S.6.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), pp. 17–18 (PDF 17–18), Proposition 5, equations (4)–(5)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Proposition 5, pp. 17–18: allocations of (2) that exhaust second-period capacity (satisfy (4)).
For `k1 ≤ k̄`, a feasible such allocation exists iff `(r + 1) p⁺_l ≤ θ`; in that case there is a
threshold `k̲` such that the optimal program spending among them is `min(p̃_b, θ/(r + 1))` for
`k1 ≤ k̲` (`p̃_b` a maximizer of `J_b` on `[p⁺_l, p⁺_u]`) and `min(p⁺_u, θ/(r + 1))` for `k1 > k̲`. -/
theorem proposition_5 (P : Params) (hP : P.Standing) :
    (∀ k1, P.Admissible k1 → P.BelowKbar k1 → ∀ pl pu : ℝ, P.PlusSet k1 = Set.Icc pl pu →
      ((∃ p a f, P.Feasible2 k1 p a f ∧ P.Eq4 k1 p a) ↔ (P.r + 1) * pl ≤ P.theta k1)) ∧
    ∃ kunder : ℝ, ∀ k1, P.Admissible k1 → P.BelowKbar k1 →
      ∀ (pl pu : ℝ) (aHat : ℝ → ℝ), P.PlusSet k1 = Set.Icc pl pu → P.IsAHat k1 pl pu aHat →
        (P.r + 1) * pl ≤ P.theta k1 →
        ∀ p a f, P.IsOptimalExh k1 p a f →
          (k1 ≤ kunder → ∀ pb ∈ Set.Icc pl pu, IsMaxOn (P.Jb k1 aHat) (Set.Icc pl pu) pb →
            p = min pb (P.theta k1 / (P.r + 1))) ∧
          (kunder < k1 → p = min pu (P.theta k1 / (P.r + 1))) := by sorry

end NonprofitFunds.Capacity
