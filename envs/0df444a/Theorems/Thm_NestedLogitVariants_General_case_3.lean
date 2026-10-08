-- Prove2me | Theorems.Thm_NestedLogitVariants_General_case_3
-- name    : NestedLogitVariants.General.case_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:43:10.145499+00:00
-- url     : https://prove2.me/theorems/d83cce36-fc2e-4388-a315-053e7d7dc409
-- title:
--   A.4 Case 3, pp. 48–49 — for γ_i ≤ 1, (2x̂, 2ŷ) and hence (βx̂, βŷ) satisfy the constraints of (3) in nest i
-- statement:
--   Let the instance satisfy the standing assumptions with $\bar\gamma>1$, let $\beta$ be the factor (12), and let $(\hat x,\hat y)$ be an optimal solution of (4) with the collection $\{N^k_{ij} : k\in N,\ j=0,\dots,k\}\cup\{\{j\}:j\in N\}$ in every nest. If nest $i$ has $\gamma_i\le1$, then for all $S_i\subseteq N$
--   $$
--   2\,\hat y_i\ \ge\ V_i(S_i)^{\gamma_i}\big(R_i(S_i)-2\,\hat x\big)\qquad\text{and}\qquad \beta\,\hat y_i\ \ge\ V_i(S_i)^{\gamma_i}\big(R_i(S_i)-\beta\,\hat x\big).
--   $$
--   The first bound is the reasoning of the proof of Theorem 10 applied to nest $i$; the second follows from it because $\beta/2\ge1$.
--
--   This is the third of the three cases of the proof of Theorem 11. It covers the nests with $\gamma_i\le1$, whatever their no-purchase weight $v_{i0}$.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), pp. 48–49, Appendix A.4, Case 3

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Factor

namespace NestedLogitVariants.General

/-- Appendix A.4, Case 3 (pp. 48–49): in a nest with `γ_i ≤ 1`,
`2 ŷ_i ≥ V_i(S)^{γ_i} (R_i(S) − 2 x̂)` and `β ŷ_i ≥ V_i(S)^{γ_i} (R_i(S) − β x̂)` for every `S ⊂ N`. -/
theorem case_3 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i) (β : ℝ) (hβ : IsGreatest (betaSet I) β)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh)
    (i : ι) (hγi : I.γ i ≤ 1) :
    (∀ S : Finset (Fin n), nestWeight I i S * (R I i S - 2 * xh) ≤ 2 * yh i) ∧
      ∀ S : Finset (Fin n), nestWeight I i S * (R I i S - β * xh) ≤ β * yh i := by sorry

end NestedLogitVariants.General
