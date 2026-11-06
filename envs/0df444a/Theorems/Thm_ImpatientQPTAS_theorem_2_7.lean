-- Prove2me | Theorems.Thm_ImpatientQPTAS_theorem_2_7
-- name    : ImpatientQPTAS.theorem_2_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:59:36.19277+00:00
-- url     : https://prove2.me/theorems/9aa8e276-fae7-44f0-af94-365f2d6894f2
-- title:
--   Theorem 2.7 — smaller departure probabilities cannot hurt
-- statement:
--   Let $r\ge0$, and let $p^-,p^+\in[0,1]^n$ with $p^-_i\le p^+_i$ for all $i$. For any adaptive policy $S$ and any start set $B$, there is an adaptive policy $S^\downarrow$ with
--   $$
--   R^{(p^-)}_B(S^\downarrow)\ge R^{(p^+)}_B(S).
--   $$
--
--   Moving back from rounded-up to smaller departure probabilities loses nothing.
--
--   Differences from the source:
--   - generalization: the start state [n] → any start set B; reason: B = [n] is the printed statement; the proof of Theorem 2.6 applies it to subsets
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Theorem 2.7, p.12; proof App. A.6

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Theorem 2.7, p.12: if `p⁻_i ≤ p⁺_i` for all `i`, then for any adaptive
policy `S` there is a policy `S↓` with `R^(p⁻)(S↓) ≥ R^(p⁺)(S)`.

**Formalization Note.** The start set `B` generalizes the printed `[n]` (`B = univ` is the printed
statement). `S↓` is a function of the state, as §1.1 asks. -/
theorem theorem_2_7 {n : ℕ} (r pm pp : Fin n → ℝ) (hr : ∀ i, 0 ≤ r i) (hm : ∀ i, 0 ≤ pm i)
    (hmp : ∀ i, pm i ≤ pp i) (hp : ∀ i, pp i ≤ 1) (S : Policy n) (hS : IsPolicy S)
    (B : Finset (Fin n)) :
    ∃ Sd : Policy n, IsPolicy Sd ∧
      (⟨r, pp⟩ : Instance n).Rfrom S B ≤ (⟨r, pm⟩ : Instance n).Rfrom Sd B := by sorry

end ImpatientQPTAS
