-- Prove2me | Theorems.Thm_NonprofitFunds_Capacity_lemma_S6
-- name    : NonprofitFunds.Capacity.lemma_S6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T05:52:06.205743+00:00
-- url     : https://prove2.me/theorems/3b4267fc-5132-4e48-a81a-a3b40b1f25e3
-- title:
--   Lemma S.6, p. S8 (PDF 37) — a capacity threshold k̲: interior first-order maximizer of J_b below it, p⁺_u above
-- statement:
--   Fix the data. There is a capacity threshold $\underline k$ with the following property. Let $k_1$ be admissible with $k_1\le\bar k$, let $[p^+_l,p^+_u]=\{p\in[0,\hat B_1]:(r+1)\hat B_2(p,0)\ge k_1\}$, and let $\hat a$ solve equation (4) with $0\le\hat a(p)\le\hat B_1-p$ for every $p\in[p^+_l,p^+_u]$. Consider
--   $$J_b(p_1)=(r+1)p_1+\mathbb E_\Psi\Big[\min\big(\Psi,(r+1)\hat B_2(p_1,\hat a(p_1))\big)\Big].$$
--   1. (a) If $k_1<\underline k$, then $J_b$ attains its maximum over $[p^+_l,p^+_u]$ at a point $\tilde p_b\in(p^+_l,p^+_u)$ with $J_b'(\tilde p_b)=0$, and $\tilde p_b$ is the only point of $(p^+_l,p^+_u)$ at which $J_b'$ vanishes.
--   2. (b) If $k_1\ge\underline k$, then $J_b$ attains its maximum over $[p^+_l,p^+_u]$ at $p_1=p^+_u$.
--
--   The threshold $\underline k$ separates the capacities at which it pays to expand capacity (an interior program level with positive $\hat a$) from those at which the nonprofit spends just enough on program to exhaust its existing capacity.
--
--   **Formalization Note.** The page puts the boundary case $k_1=\underline k$ in (a); there the first-order root is $p^+_u$ itself, which is not in the open interval $(p^+_l,p^+_u)$, so the boundary is moved to (b). The first-order condition is stated as `HasDerivAt J_b 0 p`. "$k_1\le\bar k$" is stated as in Lemma S.5.
-- source:
--   Kotsi, Aflaki, Aydin & Pedraza-Martinez, Allocation of nonprofit funds among program, fundraising, and administration, SSRN 3460795 (blinded MSOM submission), p. S8 (PDF 37), Lemma S.6; J_b is (5), p. 17 (PDF 17)

import Mathlib
import Definitions.Def_NonprofitFunds_Capacity_Model

namespace NonprofitFunds.Capacity

/-- Lemma S.6, p. S8: there is a capacity threshold `k̲` such that, for `k1 ≤ k̄`:
(a) if `k1 < k̲`, `J_b` attains its maximum over `[p⁺_l, p⁺_u]` at the unique `p1 ∈ (p⁺_l, p⁺_u)`
satisfying the first-order condition; (b) if `k1 ≥ k̲`, at `p1 = p⁺_u`. -/
theorem lemma_S6 (P : Params) (hP : P.Standing) :
    ∃ kunder : ℝ, ∀ k1, P.Admissible k1 → P.BelowKbar k1 →
      ∀ (pl pu : ℝ) (aHat : ℝ → ℝ), P.PlusSet k1 = Set.Icc pl pu → P.IsAHat k1 pl pu aHat →
        (k1 < kunder →
          ∃ p ∈ Set.Ioo pl pu, HasDerivAt (P.Jb k1 aHat) 0 p ∧
            (∀ q ∈ Set.Ioo pl pu, HasDerivAt (P.Jb k1 aHat) 0 q → q = p) ∧
            IsMaxOn (P.Jb k1 aHat) (Set.Icc pl pu) p) ∧
        (kunder ≤ k1 → IsMaxOn (P.Jb k1 aHat) (Set.Icc pl pu) pu) := by sorry

end NonprofitFunds.Capacity
