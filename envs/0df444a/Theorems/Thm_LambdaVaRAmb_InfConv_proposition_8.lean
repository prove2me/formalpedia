-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_proposition_8
-- name    : LambdaVaRAmb.InfConv.proposition_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:55.186768+00:00
-- url     : https://prove2.me/theorems/c6e542c1-1e79-4d9f-b238-1f55162358ea
-- title:
--   Proposition 8 — □ ΛᵢVaR^{wᵢ} is induced by 𝒜^{𝚲,𝐰}ₓ, has tail-splitting optimal allocations, and is a ΛVaR^w with Λ ∈ ℋ*_I when all Λᵢ increase
-- statement:
--   Let $n\ge1$, let $\Lambda_1,\dots,\Lambda_n:\mathbb R\to(0,1)$ with $\lambda^-_i=\inf_x\Lambda_i(x)>0$, and let $w_1,\dots,w_n$ be continuous capacities. Write $\boldsymbol\Lambda=(\Lambda_1,\dots,\Lambda_n)$, $\mathbf w=(w_1,\dots,w_n)$ and
--   $$
--   \mathcal A^{\boldsymbol\Lambda,\mathbf w}_x=\Big\{\bigcup_{i=1}^nA_i:A_i\in\mathcal F,\ w_i(A_i)\le\Lambda_i(y_i),\ i\in[n],\ \textstyle\sum_iy_i=x\Big\}.
--   $$
--   Then:
--
--   1. for every $X\in\mathcal X$,
--   $$
--   \mathop{\square}_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}(X)=\inf\{x\in\mathbb R:\{X>x\}\in\mathcal A^{\boldsymbol\Lambda,\mathbf w}_x\}; \tag{9}
--   $$
--   2. if the right-hand side of (9) admits a minimizer $x^*$, then there exist $(y^*_i)\in\mathbb R^n$ and $(A^*_i)\in\Pi_n(\Omega)$ with $\sum_iy^*_i=x^*$ and $w_i(\{X>x^*\}\cap A^*_i)\le\Lambda_i(y^*_i)$ for all $i$, and for every such choice the allocation
--   $$
--   X_i=(X-x^*)\,\mathbb 1_{A^*_i}+y^*_i,\qquad i\in[n], \tag{10}
--   $$
--   is an optimal allocation of $X$;
--   3. if every $\Lambda_i$ is increasing, there exist an increasing $\Lambda:\mathbb R\to(0,1]$ and a capacity $w$ with $\mathop{\square}_{i=1}^n\Lambda_i\mathrm{VaR}^{w_i}=\Lambda\mathrm{VaR}^w$ on $\mathcal X$.
--
--   The proposition identifies the inf-convolution of Lambda Value-at-Risk under heterogeneous capacities and gives optimal risk-sharing arrangements: each agent receives a cash amount plus the tail of the total risk on one part of a partition.
--
--   **Formalization Note** The paper's last sentence also claims that for decreasing $\Lambda_i$ the inf-convolution is a $\Lambda\mathrm{VaR}^w$ with $\Lambda\in\mathcal H^*_D$; that claim is false (in the Lebesgue example of the monotonicity milestone the required $\Lambda$ would jump at every point of an interval) and is not posed. $n\ge1$ is implicit ("$n$ agents"). "Admits a minimizer" means the infimum in (9) is attained at a real $x^*$; the existence clause keeps the allocation statement from being vacuous. In part 3 the pair $(\Lambda,w)$ is chosen once for all $X\in\mathcal X$. Finiteness of each $\Lambda_i\mathrm{VaR}^{w_i}$ is not assumed: it follows from $\lambda^-_i>0$ and continuity of $w_i$ (Remark 1).
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 16, Proposition 8, (9), (10)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem proposition_8 {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (Λ : Fin n → ℝ → ℝ) (w : Fin n → Set Ω → ℝ)
    (hΛ : ∀ i, LambdaVaRAmb.Robust.InH (Λ i)) (hlow : ∀ i, 0 < sInf (Set.range (Λ i)))
    (hw : ∀ i, IsContinuousCapacity (w i)) :
    (∀ X ∈ dom,
        infConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = inducedRM (capFamily Λ w) X) ∧
    (∀ X ∈ dom, ∀ xstar : ℝ,
      IsLeast {x : ℝ | {ω | x < X ω} ∈ capFamily Λ w x} xstar →
        (∃ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar ∧ IsMeasPartition A ∧
            ∀ i, w i ({ω | xstar < X ω} ∩ A i) ≤ Λ i (y i)) ∧
        (∀ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar → IsMeasPartition A →
            (∀ i, w i ({ω | xstar < X ω} ∩ A i) ≤ Λ i (y i)) →
            IsOptimalAllocation dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X
              (tailAllocation X xstar y A))) ∧
    ((∀ i, Monotone (Λ i)) →
      ∃ Λ' : ℝ → ℝ, InHStarI Λ' ∧ ∃ w' : Set Ω → ℝ, LambdaVaRAmb.Robust.IsCapacity w' ∧
        ∀ X ∈ dom, infConv dom (fun i => LambdaVaRAmb.Robust.LVaR (Λ i) (w i)) X = LambdaVaRAmb.Robust.LVaR Λ' w' X) := by sorry

end LambdaVaRAmb.InfConv
