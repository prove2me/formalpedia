-- Prove2me | Theorems.Thm_NestedLogitVariants_General_xh_nonneg
-- name    : NestedLogitVariants.General.xh_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:42:15.143045+00:00
-- url     : https://prove2.me/theorems/06f59bd4-3acf-4b34-a178-2eda1a76c2cc
-- title:
--   A.4, p. 46 — the optimal x̂ of the restricted LP (4) with the collection {N^k_ij} ∪ {{j}} is nonnegative
-- statement:
--   Consider a nested logit instance satisfying the standing assumptions, with $\bar\gamma=\max_i\gamma_i>1$ (the standing assumption of §6). Let $(\hat x,\hat y)$ be an optimal solution of the linear program (4) in which the candidate collection of every nest $i$ is $\{N^k_{ij} : k\in N,\ j=0,\dots,k\}\cup\{\{j\}:j\in N\}$. Then
--   $$
--   \hat x\ \ge\ 0 .
--   $$
--
--   This is the first step of the proof of Theorem 11; the cases of that proof multiply constraints by $\hat x$ and use its sign.
--
--   **Formalization Note** The page states this for the optimal solution of (4) and gives no further hypotheses; none is added here (in particular no $n\ge1$: for $n=0$ an optimal solution of (4) does not exist when there is a nest).
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 46, Appendix A.4, first paragraph

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR

namespace NestedLogitVariants.General

/-- Appendix A.4 (p. 46): an optimal solution `(x̂, ŷ)` of (4) with the candidate collections
`{N^k_ij} ∪ {{j}}` has `x̂ ≥ 0`. -/
theorem xh_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh) :
    0 ≤ xh := by sorry

end NestedLogitVariants.General
