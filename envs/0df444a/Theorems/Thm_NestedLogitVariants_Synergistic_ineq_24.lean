-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_ineq_24
-- name    : NestedLogitVariants.Synergistic.ineq_24
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:41:38.881308+00:00
-- url     : https://prove2.me/theorems/da08f0ed-31f6-462f-a4c1-b0035b3ba2a6
-- title:
--   (24), Appendix A.1, p. 43 — α ŷ_i bounds the objective of (8) at a fractional nested-by-revenue vector, Case k ≥ 2
-- statement:
--   Let $(\hat x, \hat y)$ be an optimal solution of (4) over the nested-by-revenue assortments $\{N_{ij} : j \in N_+\}$ for an instance with fully-captured nests, positive revenues and $\gamma_l > 1$ for some nest $l$, and let $\alpha$ be the expression in (6). For every nest $i$, every $k$ with $2 \le k \le n$ and every $\rho \in [0,1]$,
--
--   $$\alpha\, \hat y_i \ge (q_{i,k-1} + v_{ik}\rho)^{\gamma_i} \left[\frac{R_{i,k-1} + r_{ik} v_{ik} \rho}{q_{i,k-1} + v_{ik}\rho} - \alpha\, \hat x\right], \tag{24}$$
--
--   where $R_{ik'} = \sum_{j=1}^{k'} r_{ij} v_{ij}$ and $q_{ik'} = \sum_{j=1}^{k'} v_{ij}$.
--
--   With (25), this bounds $\alpha \hat y_i$ from below by the objective of (8) at every vector of the shape of Lemma 6, evaluated at $\alpha \hat x$.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The positive revenues $r_{ij} > 0$ are the disclosed pin of this mission: they keep every denominator $R_i(N_{ij})$, $j \ge 1$, of (6) positive. Product $k$ of the page (indexed from $1$) is `⟨k - 1, _⟩ : Fin n`; $R_{i,k-1}$ and $q_{i,k-1}$ are the sums over $N_{i,k-1}$. The number $\alpha$ is given together with the hypothesis that it is the greatest element of the set of terms of (6).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 43, Appendix A.1, display (24)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Factor
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation

namespace NestedLogitVariants.Synergistic

/-- Inequality (24), Appendix A.1, p. 43: for `2 ≤ k ≤ n` and `ρ ∈ [0, 1]`, with `α` the expression
in (6), `α ŷ_i ≥ (q_{i,k−1} + v_{ik} ρ)^{γ_i} [(R_{i,k−1} + r_{ik} v_{ik} ρ)/(q_{i,k−1} + v_{ik} ρ) − α x̂]`.
Product `k` (1-based) is `⟨k - 1, _⟩ : Fin n`. -/
theorem ineq_24 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    α * yh i ≥
      (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i *
        ((Rsum I i (k - 1) + I.r i ⟨k - 1, by omega⟩ * I.v i ⟨k - 1, by omega⟩ * ρ) / (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) -
          α * xh) := by sorry

end NestedLogitVariants.Synergistic
