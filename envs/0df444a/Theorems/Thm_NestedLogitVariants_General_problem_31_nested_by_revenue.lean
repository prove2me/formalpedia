-- Prove2me | Theorems.Thm_NestedLogitVariants_General_problem_31_nested_by_revenue
-- name    : NestedLogitVariants.General.problem_31_nested_by_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:43:18.995242+00:00
-- url     : https://prove2.me/theorems/5c448655-7110-4a85-9bd2-851f432f74bf
-- title:
--   A.4 Case 2, p. 48 — for γ_i > 1 and a negative coefficient, problem (31) has a nested-by-revenue optimum
-- statement:
--   Fix a nest $i$ of an instance satisfying the standing assumptions, with $\gamma_i>1$ and $v_{i0}>0$. Let $a$ be any real number and $b<0$. Then the problem
--   $$
--   \max_{z_i\in[0,1]^n}\ \sum_{j\in N}r_{ij}v_{ij}z_{ij}-a\Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)-b\Big(v_{i0}+\sum_{j\in N}v_{ij}z_{ij}\Big)^{1-\gamma_i}
--   $$
--   has an optimal solution that is the indicator vector of a nested-by-revenue assortment $\{1,2,\dots,k\}$ for some $k\in\{0,\dots,n\}$.
--
--   On the page this is problem (31) with $a=\beta\hat x$ and $b=\beta\hat y_i<0$; its nested-by-revenue optimum lets the constraint of (4) for $N^n_{ik}$ control every assortment of nest $i$ in Case 2 of the proof of Theorem 11.
--
--   **Formalization Note** The claim is stated for every $a$ and every $b<0$, which is what the page's argument uses. The hypothesis $v_{i0}>0$ is added. Case 2 ($\hat y_i<0$) arises only in partially-captured nests: in a fully-captured nest the constraint of (4) for $\emptyset=N^1_{i0}$ forces $\hat y_i\ge0$. For $v_{i0}=0$ the page's objective is $+\infty$ near $z=0$, while Lean's `rpow` gives $0^{1-\gamma_i}=0$ at $z=0$, so the problem would have no maximizer.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 48, Appendix A.4, Case 2, problem (31) and the claim that follows it

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_Relaxation

namespace NestedLogitVariants.General

/-- Appendix A.4, Case 2 (p. 48): in a partially-captured nest (`v_{i0} > 0`) with `γ_i > 1`, for
every `a` and every `b < 0` (the page has `a = β x̂`, `b = β ŷ_i`), problem (31)
`max_{z ∈ [0,1]^n} ∑_j r_{ij} v_{ij} z_j − a (v_{i0} + ∑_j v_{ij} z_j) − b (v_{i0} + ∑_j v_{ij} z_j)^{1−γ_i}`
has an optimal solution that is the indicator of a nested-by-revenue assortment `{1, …, j}`. -/
theorem problem_31_nested_by_revenue {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (i : ι) (hγi : 1 < I.γ i) (hvi : 0 < I.vnp i) (a b : ℝ) (hb : b < 0) :
    ∃ j ≤ n, ∀ z ∈ box n,
      F31 I i z a b ≤ F31 I i (fun l => if l ∈ nbr n j then 1 else 0) a b := by sorry

end NestedLogitVariants.General
