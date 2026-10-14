-- Prove2me | Theorems.Thm_LambdaVaRAmb_InfConv_theorem_3_allocation
-- name    : LambdaVaRAmb.InfConv.theorem_3_allocation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:59.281852+00:00
-- url     : https://prove2.me/theorems/f1c13591-e3a5-4c39-be8d-8228c3fc8d12
-- title:
--   Theorem 3 (8) — a minimizer x* of (7) yields the optimal allocation Xᵢ = (X − x*)𝟙_{A*ᵢ} + y*ᵢ
-- statement:
--   In the setting of Theorem 3 ($n\ge1$, families of downsets $\{\mathcal A^{(i)}_x\}$ whose induced risk measures $\rho_i$ are $<\infty$ on $\mathcal X$), let $X\in\mathcal X$ and suppose $x^*$ is a minimizer of the right-hand side of (7), i.e. $\{X>x^*\}\in\widetilde{\mathcal A}_{x^*}$ and $x^*\le x$ whenever $\{X>x\}\in\widetilde{\mathcal A}_x$. Then:
--
--   1. there exist $(y^*_1,\dots,y^*_n)\in\mathbb R^n$ and $(A^*_1,\dots,A^*_n)\in\Pi_n(\Omega)$ with $\sum_iy^*_i=x^*$ and $\{X>x^*\}\cap A^*_i\in\mathcal A^{(i)}_{y^*_i}$ for all $i$;
--   2. for any such $(y^*_i)$ and $(A^*_i)$, the allocation
--   $$
--   X_i=(X-x^*)\,\mathbb 1_{A^*_i}+y^*_i,\qquad i\in[n],
--   $$
--   belongs to $\mathbb A_n(X)$ and is optimal: $\sum_i\rho_i(X_i)=\mathop{\square}_{i=1}^n\rho_i(X)$.
--
--   The optimal allocation splits the tail of the risk above $x^*$ along a partition and adds cash amounts.
--
--   **Formalization Note** "Admits a minimizer" is read as: the infimum over the real set is attained. Item 1 makes explicit that the data in (8) exist, so item 2 is not vacuous.
-- source:
--   Liu and Schied, Lambda Value-at-Risk under ambiguity and risk sharing, arXiv:2511.00717v1, p. 15, Theorem 3, (8)

import Mathlib
import Definitions.Def_LambdaVaRAmb_InfConv_Setting

namespace LambdaVaRAmb.InfConv

theorem theorem_3_allocation {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n)
    (dom : Set (Ω → ℝ)) (hdom : IsRVDomain dom) (𝒜 : Fin n → ℝ → Set (Set Ω))
    (h𝒜 : ∀ i x, IsDownset (𝒜 i x)) (hfin : ∀ i, ∀ X ∈ dom, inducedRM (𝒜 i) X ≠ ⊤) :
    ∀ X ∈ dom, ∀ xstar : ℝ,
      IsLeast {x : ℝ | {ω | x < X ω} ∈ convFamily 𝒜 x} xstar →
        (∃ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar ∧ IsMeasPartition A ∧
            ∀ i, {ω | xstar < X ω} ∩ A i ∈ 𝒜 i (y i)) ∧
        (∀ (y : Fin n → ℝ) (A : Fin n → Set Ω), ∑ i, y i = xstar → IsMeasPartition A →
            (∀ i, {ω | xstar < X ω} ∩ A i ∈ 𝒜 i (y i)) →
            IsOptimalAllocation dom (fun i => inducedRM (𝒜 i)) X (tailAllocation X xstar y A)) := by sorry

end LambdaVaRAmb.InfConv
