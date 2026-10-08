-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_ineq_20
-- name    : NestedLogitVariants.Synergistic.ineq_20
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:40:59.130976+00:00
-- url     : https://prove2.me/theorems/390dc2f5-0ca7-4438-aeb0-6a50f9d338e3
-- title:
--   (20), Appendix A.1, Case 1.a, pp. 41–42 — the inequality with α¹_ik = R_i(N_i,k−1)/R_i(N_ik)
-- statement:
--   Let $(\hat x, \hat y)$ be an optimal solution of (4) over the nested-by-revenue assortments $\{N_{ij} : j \in N_+\}$ for an instance with fully-captured nests and positive revenues. Fix a nest $i$, an index $k$ with $2 \le k \le n$ and $\rho \in [0, 1]$, write $R_{ik'} = \sum_{j=1}^{k'} r_{ij} v_{ij}$, $q_{ik'} = \sum_{j=1}^{k'} v_{ij}$ and
--
--   $$\alpha^1_{ik} = \frac{R_i(N_{i,k-1})}{R_i(N_{ik})}.$$
--
--   Then
--
--   $$\alpha^1_{ik}\, \hat y_i \ge (q_{i,k-1} + v_{ik}\rho)^{\gamma_i} \left[\frac{R_{i,k-1} + r_{ik} v_{ik} \rho}{q_{i,k-1} + v_{ik}\rho} - \alpha^1_{ik}\, \hat x\right]. \tag{20}$$
--
--   The right side is the objective of (8) at the fractional nested-by-revenue vector with $z_{i1} = \dots = z_{i,k-1} = 1$, $z_{ik} = \rho$, evaluated at $\alpha^1_{ik} \hat x$; (20) is the first of the two bounds combined in the proof of Theorem 7.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The positive revenues $r_{ij} > 0$ are the disclosed pin of this mission: they keep every denominator $R_i(N_{ij})$, $j \ge 1$, of (6) positive. Product $k$ of the page (indexed from $1$) is `⟨k - 1, _⟩ : Fin n`; $R_{i,k-1}$ and $q_{i,k-1}$ are the sums over $N_{i,k-1}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 41–42, Appendix A.1, Case 1.a, display (20)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Relaxation

namespace NestedLogitVariants.Synergistic

/-- Inequality (20), Appendix A.1, Case 1.a, pp. 41–42: for `2 ≤ k ≤ n` and `ρ ∈ [0, 1]`, with
`α¹_{ik} = R_i(N_{i,k−1}) / R_i(N_{ik})`,
`α¹_{ik} ŷ_i ≥ (q_{i,k−1} + v_{ik} ρ)^{γ_i} [(R_{i,k−1} + r_{ik} v_{ik} ρ)/(q_{i,k−1} + v_{ik} ρ) − α¹_{ik} x̂]`.
Product `k` (1-based) is `⟨k - 1, _⟩ : Fin n`. -/
theorem ineq_20 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (k : ℕ) (hk2 : 2 ≤ k) (hkn : k ≤ n) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    (R I i (nbr n (k - 1)) / R I i (nbr n k)) * yh i ≥
      (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) ^ I.γ i *
        ((Rsum I i (k - 1) + I.r i ⟨k - 1, by omega⟩ * I.v i ⟨k - 1, by omega⟩ * ρ) / (qsum I i (k - 1) + I.v i ⟨k - 1, by omega⟩ * ρ) -
          (R I i (nbr n (k - 1)) / R I i (nbr n k)) * xh) := by sorry

end NestedLogitVariants.Synergistic
