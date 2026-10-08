-- Prove2me | Theorems.Thm_NestedLogitVariants_General_theorem_11
-- name    : NestedLogitVariants.General.theorem_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:43:09.082918+00:00
-- url     : https://prove2.me/theorems/6116d868-ab86-4be8-87e4-ebeb6dd84257
-- title:
--   Theorem 11, p. 26 — the LP optimum over {N^k_ij} ∪ {{j}}, scaled by the factor (12), is feasible for the full LP (3)
-- statement:
--   Consider the assortment problem under the nested logit model with no restriction on the dissimilarity parameters $\gamma_i$ or on the no-purchase weights $v_{i0}$ of the nests, except the standing assumption of §6 that $\bar\gamma=\max_{i\in M}\gamma_i>1$.
--
--   Let $(\hat x,\hat y)$ be an optimal solution to problem (4) when the collection of candidate assortments of every nest $i$ is
--   $$
--   \{N^k_{ij} : k\in N,\ j=0,\dots,k\}\cup\{\{j\} : j\in N\},
--   $$
--   where $N^k_{ij}$ consists of the $j$ highest-revenue products among the $k$ products of nest $i$ with the smallest preference weights. Let $\beta$ denote the expression in (12),
--   $$
--   \beta=\max_{i\in M^f,\ j=2,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\vee\max_{i\in M^p,\ j=1,\dots,n}\left\{\frac{V_i(N_{ij})}{V_i(N_{i,j-1})}\right\}\vee2 .
--   $$
--   Then $(\beta\hat x,\beta\hat y)$ is a feasible solution to problem (3): $v_0\,\beta\hat x\ge\sum_{i\in M}\beta\hat y_i$, and
--   $$
--   \beta\,\hat y_i\ \ge\ V_i(S_i)^{\gamma_i}\big(R_i(S_i)-\beta\,\hat x\big)\qquad\text{for all } S_i\subseteq N,\ i\in M.
--   $$
--
--   Combined with Theorem 1, this shows that solving a linear program with $1+m$ variables and $1+m(1+n+n^2)$ constraints yields an assortment whose expected revenue is within the factor $\beta$ of the optimum, for the most general instances of the problem.
--
--   **Formalization Note** The standing assumptions are those of the shared model ($v_{ij}>0$, $r_{ij}\ge0$, $\gamma_i>0$, revenues ordered), plus `hsyn` for $\bar\gamma>1$. $\beta$ is taken as the greatest element of the finite set `betaSet I`, so $\beta\ge2$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 26, Theorem 11 (proof in Appendix A.4, pp. 46–49)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Factor

namespace NestedLogitVariants.General

/-- Theorem 11 (p. 26): let `(x̂, ŷ)` be an optimal solution of (4) with the candidate collections
`{N^k_ij : k ∈ N, j = 0, …, k} ∪ {{j} : j ∈ N}`, and let `β` be the factor (12). Then
`(β x̂, β ŷ)` is feasible for (3). -/
theorem theorem_11 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i) (β : ℝ) (hβ : IsGreatest (betaSet I) β)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    LP3Feasible I (β * xh) (β • yh) := by sorry

end NestedLogitVariants.General
