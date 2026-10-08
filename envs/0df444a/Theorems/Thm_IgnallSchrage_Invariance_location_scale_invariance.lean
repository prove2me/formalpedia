-- Prove2me | Theorems.Thm_IgnallSchrage_Invariance_location_scale_invariance
-- name    : IgnallSchrage.Invariance.location_scale_invariance
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:35:35.049373+00:00
-- url     : https://prove2.me/theorems/c6414cb9-3128-4013-ac3c-f059e1657228
-- title:
--   Appendix THEOREM (p. 411) — under $\tilde x_i=H(x'_i+G)$, $H,G>0$, same optimal sequences and same branch-and-bound path
-- statement:
--   Let $P'$ be a flow-shop problem with $n$ jobs and nonnegative processing times $a'_i,b'_i,c'_i$. Let $\tilde P$ be the problem with processing times
--   $$
--   \tilde a_i=H(a'_i+G),\qquad \tilde b_i=H(b'_i+G),\qquad \tilde c_i=H(c'_i+G)\qquad\text{for some } H,G>0 \text{ and every } i .
--   $$
--   Then, both for the three-machine makespan problem (machines $A,B,C$, lower bound of p. 401) and for the two-machine problem of least mean completion time (machines $A,B$, lower bound of p. 406):
--
--   1. **the same sequences are optimal for both problems**: a full sequence $\sigma$ minimizes the objective of $\tilde P$ over all $n!$ sequences if and only if it minimizes the objective of $P'$;
--   2. **the branch-and-bound procedure follows the same path for both problems**: for every $k$, the list of nodes after $k$ steps of the procedure of p. 402 is the same for $\tilde P$ and for $P'$.
--
--   The Appendix introduces the theorem as follows: "for the 2-machine mean completion-time or 3-machine makespan problems, changing the location and/or the scale of the processing times does not affect the solution."
--
--   **Formalization Note** The paper's loose phrases are made explicit. "The same sequence is optimal" is read as equality of the sets of optimal sequences, stated as an *iff* for every $\sigma$. "Will follow the same path" is read as equality of the procedure's lists at every step, and the procedure is the deterministic one of the definition `Procedure`. The two-machine objective is the sum $\sum_i d_i$, which has the same minimizers as the mean. Nonnegative processing times are assumed. The paper states no sign condition, but processing times are durations, and with negative times the theorem fails: $n=3$, $a'=(0,-4,-6)$, $b'=(-2,0,6)$, $c'=(0,-5,-6)$, $H=G=1$ changes the set of minimum-makespan sequences.
-- source:
--   Ignall and Schrage, Application of the branch and bound technique to some flow-shop scheduling problems, Oper. Res. 13 (1965), p. 411, Appendix, THEOREM

import Mathlib
import Definitions.Def_IgnallSchrage_Makespan_Procedure
import Definitions.Def_IgnallSchrage_Invariance_ThreeMachine
import Definitions.Def_IgnallSchrage_Invariance_TwoMachine

namespace IgnallSchrage.Invariance

/-- The THEOREM of the Appendix (p. 411). If the processing times of two flow-shop problems `P̃`
and `P'` are related by `ã_i = H (a'_i + G)`, `b̃_i = H (b'_i + G)`, `c̃_i = H (c'_i + G)` with
`H, G > 0` (processing times `a'_i, b'_i, c'_i ≥ 0`), then (1) the same sequences are optimal for both problems and (2) the
branch-and-bound procedure follows the same path for both, for the three-machine makespan problem
(with the lower bound of p. 401) and the two-machine sum-of-completion-times problem (with the
lower bound of p. 406). -/
theorem location_scale_invariance {n : ℕ} (a' b' c' : Fin n → ℝ)
    (ha : ∀ i, 0 ≤ a' i) (hb : ∀ i, 0 ≤ b' i) (hc : ∀ i, 0 ≤ c' i) (H G : ℝ)
    (hH : 0 < H) (hG : 0 < G) :
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') σ ≤
          IgnallSchrage.Makespan.makespan (shiftScale H G a') (shiftScale H G b') (shiftScale H G c') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), IgnallSchrage.Makespan.makespan a' b' c' σ ≤ IgnallSchrage.Makespan.makespan a' b' c' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound3 (shiftScale H G a') (shiftScale H G b') (shiftScale H G c')) k =
        IgnallSchrage.Makespan.run (lowerBound3 a' b' c') k) ∧
    (∀ σ : Equiv.Perm (Fin n),
      (∀ τ : Equiv.Perm (Fin n),
        sumCompletion (shiftScale H G a') (shiftScale H G b') σ ≤
          sumCompletion (shiftScale H G a') (shiftScale H G b') τ) ↔
      (∀ τ : Equiv.Perm (Fin n), sumCompletion a' b' σ ≤ sumCompletion a' b' τ)) ∧
    (∀ k : ℕ,
      IgnallSchrage.Makespan.run (lowerBound2 (shiftScale H G a') (shiftScale H G b')) k =
        IgnallSchrage.Makespan.run (lowerBound2 a' b') k) := by sorry

end IgnallSchrage.Invariance
