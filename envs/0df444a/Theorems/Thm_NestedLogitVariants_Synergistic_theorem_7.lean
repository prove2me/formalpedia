-- Prove2me | Theorems.Thm_NestedLogitVariants_Synergistic_theorem_7
-- name    : NestedLogitVariants.Synergistic.theorem_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T21:41:37.513989+00:00
-- url     : https://prove2.me/theorems/d27f2288-3018-4a31-979d-e6387812f8ce
-- title:
--   Theorem 7, p. 21 — scaling the nested-by-revenue LP optimum by the factor α of (6) gives a feasible solution of (3)
-- statement:
--   Consider the nested logit assortment problem with fully-captured nests ($v_{i0} = 0$ for every nest $i$), $\gamma_i > 1$ for some nest $i$, positive revenues and $n \ge 2$ products per nest. Let $(\hat x, \hat y)$ be an optimal solution of the linear program (4) in which the candidate assortments of every nest are the nested-by-revenue assortments $\{N_{ij} : j \in N_+\}$, and let
--
--   $$\alpha = \max_{i \in M,\ j = 2, \dots, n} \left\{\frac{R_i(N_{i,j-1})}{R_i(N_{ij})} \wedge \left(\frac{R_i(N_{ij})}{R_i(N_{i,j-1})}\, \frac{V_i(N_{ij})^{\gamma_i}}{V_i(N_{i,j-1})^{\gamma_i}}\right)\right\} \tag{6}$$
--
--   with $a \wedge b = \min\{a, b\}$. Then $(\alpha \hat x, \alpha \hat y)$ is feasible for problem (3):
--
--   $$v_0\, \alpha \hat x \ge \sum_{i \in M} \alpha \hat y_i, \qquad \alpha \hat y_i \ge V_i(S_i)^{\gamma_i}\,(R_i(S_i) - \alpha \hat x) \quad \forall S_i \subseteq N,\ i \in M.$$
--
--   Combined with Theorem 1, this shows that the best combination of nested-by-revenue assortments, found by a linear program with $1 + m$ variables and $1 + m(1 + n)$ constraints, earns at least a fraction $1/\alpha$ of the optimal expected revenue.
--
--   **Formalization Note** The standing assumptions are those of the model (see the Model definition) and of §4: every nest is fully captured, $v_{i0} = 0$, and $\gamma_i > 1$ for some nest $i$ (p. 16). The positive revenues $r_{ij} > 0$ are the disclosed pin of this mission: they keep every denominator $R_i(N_{ij})$, $j \ge 1$, of (6) positive. The condition $n \ge 2$ makes the range of (6) nonempty. The number $\alpha$ is given together with the hypothesis that it is the greatest element of the set of terms of (6), not merely an upper bound. The collection $\{N_{ij} : j \in N_+\}$ is the set of `nbr n j` for $j \le n$, including $N_{i0} = \emptyset$. An optimal solution of (4) is a feasible pair whose $x$ is no larger than that of any feasible pair.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 21, Theorem 7 (proof in Appendix A.1, pp. 41–43)

import Mathlib
import Definitions.Def_NestedLogitVariants_Synergistic_Factor

namespace NestedLogitVariants.Synergistic

/-- Theorem 7, p. 21: let `(x̂, ŷ)` be an optimal solution of problem (4) with the candidate
collections replaced by the nested-by-revenue assortments `{N_{ij} : j ∈ N_+}`. Then, with `α` the
expression in (6), `(α x̂, α ŷ)` is a feasible solution of problem (3). -/
theorem theorem_7 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing) (hfc : ∀ i, I.vnp i = 0) (hsyn : ∃ i, 1 < I.γ i)
    (hr : ∀ i j, 0 < I.r i j) (hn : 2 ≤ n)
    (α : ℝ) (hα : IsGreatest (alphaTerms I) α)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (fun _ => {S | ∃ j ≤ n, S = nbr n j}) xh yh) :
    LP3Feasible I (α * xh) (α • yh) := by sorry

end NestedLogitVariants.Synergistic
