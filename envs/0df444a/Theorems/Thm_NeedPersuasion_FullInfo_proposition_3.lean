-- Prove2me | Theorems.Thm_NeedPersuasion_FullInfo_proposition_3
-- name    : NeedPersuasion.FullInfo.proposition_3
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-10-16T01:05:49.328411+00:00
-- url     : https://prove2.me/theorems/81e779fd-c749-4cdc-b02b-b4165ecb279e
-- title:
--   Proposition 3(1)–(2), p. 18 — information design Pareto-dominates full information iff λ_L ≥ Λ̄_L(λ_H), with explicit lower bound and gain factors β_{L,sm}, β_{H,sm}
-- statement:
--   Fix $\lambda_H\in(0,1)$ and utilities $u_L,u_H$ such that, for every $\lambda_L\in(0,1-\lambda_H]$, the model $(\lambda_L,\lambda_H,u_L,u_H)$ satisfies the standing assumptions. Assume moreover that $\sum_n\lambda_H^nu_H(n)$ converges and that $u_L(m_{fi}-1)\neq0$. Then there is a threshold $\bar\Lambda_L(\lambda_H)\in(0,1-\lambda_H]$, the same in both parts, with
--   $$\bar\Lambda_L(\lambda_H)\;\ge\;(1-\lambda_H)\,\frac{u_L(m_{fi}-1)}{u_L(0)-\sum_{k=1}^{m_{fi}-1}\lambda_H^k\big(u_L(k-1)-u_L(k)\big)}\;>\;0,$$
--   such that:
--   1. for every $\lambda_L\in(0,1-\lambda_H]$ with $\lambda<1$, or with $u_L,u_H\to-\infty$: some signaling mechanism Pareto-dominates the full-information mechanism $\mathsf{fi}$ if and only if $\lambda_L\ge\bar\Lambda_L(\lambda_H)$;
--   2. for every $\lambda_L\ge\bar\Lambda_L(\lambda_H)$ with $\lambda<1$, if $u_L(m_{fi}-1)\le W_L(\mathsf{fi})$, $u_H(m_{fi})\le W_H(\mathsf{fi})$, $L(m_{fi}-1)\le0$ and $W_H(\mathsf{fi})>0$, then $\beta_{L,sm}>1$, $\beta_{H,sm}>1$, and there is a signaling mechanism $\mathsf{sm}\in\Pi_{SM}$ with
--   $$W_L(\mathsf{sm})\ge\beta_{L,sm}\,W_L(\mathsf{fi})\qquad\text{and}\qquad W_H(\mathsf{sm})\ge\beta_{H,sm}\,W_H(\mathsf{fi}),$$
--   where $\beta_{L,sm}=1+\frac{\lambda_H(1-\lambda)\lambda_L\lambda^{m_{fi}-1}}{1-\lambda_H-\lambda_L\lambda^{m_{fi}-1}}$ and $\beta_{H,sm}=1+\frac{(1-\lambda_H)(1-\lambda)\lambda_L\lambda^{m_{fi}-1}}{1-\lambda_H-\lambda_L\lambda^{m_{fi}-1}}$.
--
--   When low-need arrivals are frequent enough, withholding queue information lets L users internalize the congestion they impose, and both types gain over full information, by at least the explicit factors of part 2.
--
--   **Formalization Note** $\bar\Lambda_L$ is quantified once, before $\lambda_L$, with $\lambda_H,u_L,u_H$ fixed, so it cannot depend on $\lambda_L$. The page's range "$\lambda_L\in[\bar\Lambda_L(\lambda_H),1)$" is intersected with the standing assumption $\lambda\le1$, i.e. $\lambda_L\le1-\lambda_H$. Added hypotheses, all disclosed: (i) $u_L(m_{fi}-1)\neq0$, without which the claimed $\bar\Lambda_L>0$ fails (if $u_L(m_{fi}-1)=0$ then $f(0,\lambda_H)=0$ and $\mathsf{fi}$ is dominated for every small $\lambda_L$); (ii) in part 1, Lemma 2's hypothesis ($\lambda<1$, or $u_L,u_H\to-\infty$), which the proof uses through the existence of maximizers; (iii) convergence of $\sum_n\lambda_H^nu_H(n)$, the finite-welfare convention (equivalent to $\Pi_{AP}\ne\emptyset$). In part 2 the page's "$\mathsf{sm}$" is read existentially (some signaling mechanism attains both bounds; the proof's witness is the threshold mechanism $m_{fi}-1$): read over every Pareto-efficient signaling mechanism the bounds need not hold. $L(m_{fi}-1)$ is the (LEAVE) value of the threshold policy $\pi_{m_{fi}-1}$.
-- source:
--   arXiv:2005.07253v3, Proposition 3(1)–(2), p. 18

import Mathlib
import Definitions.Def_NeedPersuasion_FullInfo_Model
import Definitions.Def_NeedPersuasion_FullInfo_Constants

namespace NeedPersuasion.FullInfo

theorem proposition_3 (lamH : ℝ) (uL uH : ℕ → ℝ)
    (hlamH : 0 < lamH ∧ lamH < 1)
    (hStand : ∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH), (⟨l, lamH, uL, uH⟩ : Model).Standing)
    (hFin : Summable (fun n : ℕ => lamH ^ n * uH n))
    (hu : uL (mfiOf uL - 1) ≠ 0) :
    ∃ Λbar : ℝ, Λbar ∈ Set.Ioc (0 : ℝ) (1 - lamH) ∧
      0 < lowerBound lamH uL ∧ lowerBound lamH uL ≤ Λbar ∧
      -- Part 1
      (∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH),
        (l + lamH < 1 ∨
          (Filter.Tendsto uL Filter.atTop Filter.atBot ∧
            Filter.Tendsto uH Filter.atTop Filter.atBot)) →
        ((∃ π ∈ PiSM ⟨l, lamH, uL, uH⟩,
            Dominates ⟨l, lamH, uL, uH⟩ π (fi ⟨l, lamH, uL, uH⟩)) ↔ Λbar ≤ l)) ∧
      -- Part 2
      (∀ l ∈ Set.Ioc (0 : ℝ) (1 - lamH), Λbar ≤ l → l + lamH < 1 →
        let M : Model := ⟨l, lamH, uL, uH⟩
        M.uL (mfi M - 1) ≤ WL M (fi M) →
        M.uH (mfi M) ≤ WH M (fi M) →
        leaveValx M ((mfi M : ℝ) - 1) ≤ 0 →
        0 < WH M (fi M) →
        1 < betaL M ∧ 1 < betaH M ∧
          ∃ π ∈ PiSM M, betaL M * WL M (fi M) ≤ WL M π ∧ betaH M * WH M (fi M) ≤ WH M π) := by sorry

end NeedPersuasion.FullInfo
