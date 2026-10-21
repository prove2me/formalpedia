-- Prove2me | Theorems.Thm_LiqProvision_Oligopoly_theorem_3_8_claim_b
-- name    : LiqProvision.Oligopoly.theorem_3_8_claim_b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:41:44.488675+00:00
-- url     : https://prove2.me/theorems/70cbc80a-2563-4853-8c97-04234d40a870
-- title:
--   Proof of Theorem 3.8, claim (b), p. 23 — P″∗ is bounded and bounded away from zero, so P′∗(n) → ±∞
-- statement:
--   Assume the standing assumptions and Assumptions 2.1 and 3.7, and let $p=P_*'$ be an increasing, continuously differentiable solution of (3.8) on $\mathbb R\setminus\{0\}$. Then there are constants $0<c\le C$ with
--   $$c\le p'(n)\le C\qquad(n\ne0),$$
--   and consequently
--   $$\lim_{n\to-\infty}p(n)=-\infty,\qquad\lim_{n\to\infty}p(n)=\infty .$$
--
--   The proof of Theorem 3.11 uses it to show that every admissible deviation is compatible with $P_*$.
--
--   **Formalization Note.** The model objects are those of `LiqProvision.Oligopoly.Model`. "Derivatives" in the claim are those of $P_*'$, i.e. $P_*''$. The claim is stated for the unique solution; by Theorem 3.8 this is the same as stating it for every solution in Theorem 3.8's class.
-- source:
--   Herdegen, Muhle-Karbe and Stebegg, Liquidity Provision with Adverse Selection and Inventory Costs, arXiv:2107.12094v1, p. 23, proof of Theorem 3.8, claim (b)

import Mathlib
import Definitions.Def_LiqProvision_Oligopoly_Model

namespace LiqProvision.Oligopoly
open Filter in
theorem theorem_3_8_claim_b (M : Params) (hS : M.Standing) (h21 : M.Assumption21)
    (h37 : M.Assumption37) (p : ℝ → ℝ) (hp : IsODESol M p) :
    (∃ c C : ℝ, 0 < c ∧ ∀ n, n ≠ 0 → c ≤ deriv p n ∧ deriv p n ≤ C) ∧
      Tendsto p atBot atBot ∧ Tendsto p atTop atTop := by sorry
end LiqProvision.Oligopoly
