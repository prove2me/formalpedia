-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_ineq_25
-- name    : NestedLogitVariants.Synergistic.ineq_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:41:28.011712+00:00
-- url     : https://prove2.me/theorems/f8310a01-8f46-47ee-bad8-404fce78457c
-- title:
--   (25), Appendix A.1, Case 2, p. 43 — α ŷ_i bounds the objective of (8) when only the first product is offered fractionally
-- statement:
--   Let $(\hat x, \hat y)$ be an optimal solution of (4) over the nested-by-revenue assortments $\{N_{ij} : j \in N_+\}$ for an instance with fully-captured nests, positive revenues, $n \ge 2$ and $\gamma_l > 1$ for some nest $l$, and let $\alpha$ be the expression in (6). For every nest $i$ and every $\rho \in [0, 1]$,
--
--   $$\alpha\, \hat y_i \ge (v_{i1}\rho)^{\gamma_i} \left[\frac{r_{i1} v_{i1} \rho}{v_{i1}\rho} - \alpha\, \hat x\right]. \tag{25}$$
--
--   This is the case $k = 1$ of the bound (24).
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The positive revenues $r_{ij} > 0$ are the disclosed pin of this mission: they keep every denominator $R_i(N_{ij})$, $j \ge 1$, of (6) positive. Product $1$ of the page is `⟨0, _⟩ : Fin n`. At $\rho = 0$ the right side is $0^{\gamma_i}(0/0 - \alpha\hat x) = 0$. The condition $n \ge 2$ is the range of (6). The number $\alpha$ is given together with the hypothesis that it is the greatest element of the set of terms of (6).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 43, Appendix A.1, Case 2, display (25)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Factor

namespace NestedLogitVariants.Synergistic

/-- Inequality (25), Appendix A.1, Case 2, p. 43: for `ρ ∈ [0, 1]`, with `α` the expression in (6),
`α ŷ_i ≥ (v_{i1} ρ)^{γ_i} [r_{i1} v_{i1} ρ/(v_{i1} ρ) − α x̂]`. Product `1` is `⟨0, _⟩ : Fin n`. -/
theorem ineq_25 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (hn : 2 ≤ n)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh)
    (i : ι) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    α * yh i ≥ (I.v i ⟨0, by omega⟩ * ρ) ^ I.γ i * (I.r i ⟨0, by omega⟩ * I.v i ⟨0, by omega⟩ * ρ / (I.v i ⟨0, by omega⟩ * ρ) - α * xh) := by sorry

end NestedLogitVariants.Synergistic
