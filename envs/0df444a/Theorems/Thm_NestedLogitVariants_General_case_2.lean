-- Prove2me | Theorems.Thm_NestedLogitVariants_General_case_2
-- name    : NestedLogitVariants.General.case_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T21:42:54.398591+00:00
-- url     : https://prove2.me/theorems/9e4bba33-b00f-40df-bd72-9166ca73a6a1
-- title:
--   A.4 Case 2, p. 48 — for γ_i > 1 and ŷ_i < 0, (βx̂, βŷ) satisfies the constraints of (3) in nest i
-- statement:
--   Let the instance satisfy the standing assumptions with $\bar\gamma>1$, let $\beta$ be the factor (12), and let $(\hat x,\hat y)$ be an optimal solution of (4) with the collection $\{N^k_{ij} : k\in N,\ j=0,\dots,k\}\cup\{\{j\}:j\in N\}$ in every nest. If nest $i$ has $\gamma_i>1$ and $\hat y_i<0$, then
--   $$
--   \beta\,\hat y_i\ \ge\ V_i(S_i)^{\gamma_i}\big(R_i(S_i)-\beta\,\hat x\big)\qquad\text{for all } S_i\subseteq N,
--   $$
--   that is, $(\beta\hat x,\beta\hat y)$ satisfies the second set of constraints of problem (3) for nest $i$.
--
--   This is the second of the three cases of the proof of Theorem 11.
-- source:
--   Davis, Gallego, Topaloglu, Assortment optimization under variants of the nested logit model, revised manuscript of June 18, 2013 (published Oper. Res. 62(2), 2014, DOI 10.1287/opre.2014.1256), p. 48, Appendix A.4, Case 2 (conclusion)

import Mathlib
import Definitions.Def_NestedLogitVariants_General_Model
import Definitions.Def_NestedLogitVariants_General_NestedPR
import Definitions.Def_NestedLogitVariants_General_Factor

namespace NestedLogitVariants.General

/-- Appendix A.4, Case 2 (p. 48): in a nest with `γ_i > 1` and `ŷ_i < 0`, the solution `(β x̂, β ŷ)` satisfies the second set of constraints of (3)
for nest `i`: `β ŷ_i ≥ V_i(S)^{γ_i} (R_i(S) − β x̂)` for every `S ⊂ N`. -/
theorem case_2 {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ} (I : Instance ι n)
    (hI : I.Standing)
    (hsyn : ∃ i, 1 < I.γ i) (β : ℝ) (hβ : IsGreatest (betaSet I) β)
    (xh : ℝ) (yh : ι → ℝ) (hopt : LP4Optimal I (candidatesPR I) xh yh)
    (i : ι) (hγi : 1 < I.γ i) (hyi : yh i < 0) :
    ∀ S : Finset (Fin n), nestWeight I i S * (R I i S - β * xh) ≤ β * yh i := by sorry

end NestedLogitVariants.General
