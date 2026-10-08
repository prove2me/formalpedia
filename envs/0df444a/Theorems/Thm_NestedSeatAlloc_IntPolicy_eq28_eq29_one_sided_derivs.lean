-- Prove2me | Theorems.Thm_NestedSeatAlloc_IntPolicy_eq28_eq29_one_sided_derivs
-- name    : NestedSeatAlloc.IntPolicy.eq28_eq29_one_sided_derivs
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T16:39:10.718489+00:00
-- url     : https://prove2.me/theorems/1c1ac1bb-6943-434b-be81-3ce3b586a4d0
-- title:
--   (28)–(29), pp. 132–133 — one-sided derivatives of ER_{k+1} in terms of those of ER_k, for integer demand
-- statement:
--   Work in the seat model with integer-valued demands $X_1, X_2, \dots$, and let $p$ be a protection-level policy ($p_k \ge 0$). Fix $k \ge 1$ and let $\delta_\pm ER_k[t; p; X]$ be the right derivative ($t \ge 0$) and left derivative ($t > 0$) of $t \mapsto ER_k[t; p; X]$, assumed to exist. Write $d[x]$ for the largest integer $\le x$ and $u[x]$ for the smallest integer $\ge x$. Then for every $s \ge p_k$,
--   $$\delta_+ ER_{k+1}[s; p; X] = f_{k+1} \Pr[X_{k+1} > s - p_k] + \sum_{i=0}^{d[s - p_k]} \delta_+ ER_k[s - i; p; X] \Pr[X_{k+1} = i], \tag{28}$$
--   and for every $s > p_k$,
--   $$\delta_- ER_{k+1}[s; p; X] = f_{k+1} \Pr[X_{k+1} \ge s - p_k] + \sum_{i=0}^{u[s - p_k - 1]} \delta_- ER_k[s - i; p; X] \Pr[X_{k+1} = i]. \tag{29}$$
--
--   These recursions propagate the derivatives of the expected revenue from the nest of the $k$ highest classes to the nest of $k+1$; the proof of Theorem 2 reads off from them that the CLBI shape is preserved and that the right derivative eventually falls below the next fare.
--
--   **Formalization Note** The page prints (28)–(29) without a range of $s$. They hold for $s \ge p_k$ (resp. $s > p_k$); for $s < p_k$ the recursion (9) gives $\delta_\pm ER_{k+1}[s] = \delta_\pm ER_k[s]$ and the printed right-hand side is wrong there, so the range is stated. The derivatives of $ER_k$ enter as functions $d_r, d_l$ assumed to be the one-sided derivatives, so no default value is ever used. The upper summation limits are $\lfloor s - p_k \rfloor$ and $\lceil s - p_k \rceil - 1$ (sums over $i = 0, \dots, \lfloor s-p_k \rfloor$ and $i = 0, \dots, \lceil s - p_k\rceil - 1$).
-- source:
--   Brumelle & McGill (1993), Operations Research 41(1), (28)–(29), proof of Theorem 2, pp. 132–133

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Definitions.Def_NestedSeatAlloc_IntPolicy_CLBI

namespace NestedSeatAlloc.IntPolicy

open MeasureTheory ProbabilityTheory

/-- (28)–(29), pp. 132–133: with integer-valued demand, if `dr t` and `dl t` are the right (`t ≥ 0`) and
left (`t > 0`) derivatives of `ER_k[·; p; X]`, then for `s ≥ p_k`
`δ₊ER_{k+1}[s] = f_{k+1} Pr[X_{k+1} > s − p_k] + Σ_{i=0}^{⌊s − p_k⌋} δ₊ER_k[s − i] Pr[X_{k+1} = i]`, and for
`s > p_k`
`δ₋ER_{k+1}[s] = f_{k+1} Pr[X_{k+1} ≥ s − p_k] + Σ_{i=0}^{⌈s − p_k⌉ − 1} δ₋ER_k[s − i] Pr[X_{k+1} = i]`. -/
theorem eq28_eq29_one_sided_derivs {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (X : ℕ → Ω → ℝ)
    (f p : ℕ → ℝ) (hM : IsSeatModel P X f) (hint : ∀ k ω, ∃ n : ℕ, X k ω = n)
    (hp : IsProtectionPolicy p) (k : ℕ) (hk : 1 ≤ k) (dr dl : ℝ → ℝ)
    (hdr : ∀ t, 0 ≤ t → HasDerivWithinAt (expRevenue P X f p k) (dr t) (Set.Ici t) t)
    (hdl : ∀ t, 0 < t → HasDerivWithinAt (expRevenue P X f p k) (dl t) (Set.Iic t) t) :
    (∀ s, p k ≤ s →
      HasDerivWithinAt (expRevenue P X f p (k + 1))
        (f (k + 1) * P.real {ω | s - p k < X (k + 1) ω} +
          ∑ i ∈ Finset.range (⌊s - p k⌋₊ + 1), dr (s - i) * P.real {ω | X (k + 1) ω = (i : ℝ)})
        (Set.Ici s) s) ∧
    (∀ s, p k < s →
      HasDerivWithinAt (expRevenue P X f p (k + 1))
        (f (k + 1) * P.real {ω | s - p k ≤ X (k + 1) ω} +
          ∑ i ∈ Finset.range ⌈s - p k⌉₊, dl (s - i) * P.real {ω | X (k + 1) ω = (i : ℝ)})
        (Set.Iic s) s) := by sorry

end NestedSeatAlloc.IntPolicy
