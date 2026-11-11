-- Prove2me | Theorems.Thm_OneTrap_Core_lemma_B_2
-- name    : OneTrap.Core.lemma_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:45:34.432987+00:00
-- url     : https://prove2.me/theorems/da9905bf-f99d-473a-844b-488724f98ea4
-- title:
--   Lemma B.2 — raising the incumbent residual leaves $U$ unchanged and weakly raises $P$
-- statement:
--   Fix $w\in W_{\mathrm{eff}}$ and a finite technology. For fixed $(R,x)$ and $h'\ge h$,
--   $$U(R,x,h')=U(R,x,h),\qquad P(R,x,h')\ge P(R,x,h).$$
--
--   Differences from the source:
--   - encoding: U(R, x, h) and P(R, x, h): the agent's optimal value from the state and the best principal value among the policies attaining it → `Ubell`/`Pbell`: the optimal values of the search problem whose openable boxes are R and whose only initially available outcome is (x, h) (agent value as a supremum over policies, principal value as `pfValue`); reason: stopping yields exactly (x, h), as u_stop = x and p_stop = h in (17); earlier outcomes are lexicographically below the incumbent and the remaining outputs are independent of the past
--   - generalization: states (R, x, h) that arise in the search: x the highest observed wage, h the largest residual at wage x (so (x, h) ≥lex (0, 0)) → every finite R ⊆ A and every real x and h; reason: the continuation problem and the argument are defined for any incumbent pair; at the states of the source this is the source's statement
-- source:
--   Feldman, Fu, Peng, Tang (2026), One Trap Is Enough: The Structure and Complexity of Robust Contracts for Sequential Search, held STOC 2027 submission (SHA-256 8b684ffb…cf066), Lemma B.2, p. 23 (PDF 24)

import Mathlib
import Definitions.Def_OneTrap_Core_Model
import Definitions.Def_OneTrap_Core_Search

open MeasureTheory

namespace OneTrap.Core

/-- Lemma B.2 (p. 23). For fixed `(R, x)` and `h' ≥ h`: `U(R, x, h') = U(R, x, h)` and
`P(R, x, h') ≥ P(R, x, h)`. -/
theorem lemma_B_2 {ι : Type*} [Fintype ι] [DecidableEq ι] (w : ℝ → ℝ) (hw : IsEffContract w)
    (T : ι → Box) (R : Finset ι) (x h h' : ℝ) (hh : h ≤ h') :
    Ubell w T R x h' = Ubell w T R x h ∧ Pbell w T R x h ≤ Pbell w T R x h' := by sorry

end OneTrap.Core
