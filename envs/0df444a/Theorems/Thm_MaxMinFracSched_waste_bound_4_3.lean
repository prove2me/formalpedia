-- Prove2me | Theorems.Thm_MaxMinFracSched_waste_bound_4_3
-- name    : MaxMinFracSched.waste_bound_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:18:12.48265+00:00
-- url     : https://prove2.me/theorems/feac6d34-9e45-425e-a55a-3bb50e860304
-- title:
--   Section 4.3 — wasted work of the worst-case family is at most $\tfrac12-\tfrac1{2k}$
-- statement:
--   Let $k\ge1$ and let $w_1,\dots,w_k\ge0$ have total $W=\sum_{i=1}^k w_i>0$. Then
--   $$\sum_{i=1}^{k}\Bigl(1-\frac{\sum_{j=1}^{i}w_j}{W}\Bigr)\frac{w_i}{W}=\frac12\Bigl(1-\frac{w_1^2+\dots+w_k^2}{W^2}\Bigr)\le\frac12-\frac1{2k}.$$
--
--   The left side is the wasted work $T_{\rm waste}=\sum_{i=1}^k\bigl(1-\hat f/\hat f(t_i)\bigr)T_i$ of ScaledEDF on the worst-case family of Section 4.3, after substituting $T_i=w_i/W$ (3) and $\hat f/\hat f(t_i)=\sum_{j\le i}w_j/W$ (4). The bound, below $1/2$ for every $k$, is what yields the ratio $1/2$.
--
--   Differences from the source:
--   - reading: W = Σ_{i=0}^{k} w_i → W = Σ_{i=1}^{k} w_i; reason: the only reading under which the printed chain is an identity; with w_0 included the step to Σ_{1≤i<j≤k} w_i w_j / W² fails
--   - encoding: the chain for T_waste with (3) and (4) substituted → the resulting algebraic identity and bound in w_1, …, w_k; reason: the chain's content after the substitutions the page makes
-- source:
--   Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, Scheduling Jobs to Maximize Minimum Fractional Completion, STOC 2027 submission (manuscript sha256 84f86375…80e0e), Section 4.3, pp.22–23 (PDF pp.24–25), Eqs. (3)–(4)

import Mathlib

namespace MaxMinFracSched

/-- **Section 4.3: the wasted work of the worst-case family.** Agrawal–Baruah–Kehne–Nirjhor–Rockwell–Wein, *Scheduling Jobs to Maximize Minimum Fractional
Completion*, STOC 2027 submission manuscript (sha256 84f86375…80e0e), Section 4.3, pp.22–23
(PDF pp.24–25), the chain from `Twaste = Σ_{i=1}^k (1 − f̂/f̂(ti)) Ti` to
`= ½(1 − (w1² + · · · + wk²)/W²) ≤ ½ − 1/(2k)`: "The final inequality comes from observing that the
previous term is maximized at w1 = · · · = wk."

With `T_i = w_i/W` (3) and `f̂/f̂(t_i) = Σ_{j≤i} w_j / W` (4) substituted, the chain is the
identity and the bound
`Σ_{i=1}^k (1 − Σ_{j=1}^i w_j / W) · w_i / W = ½ (1 − Σ_{i=1}^k w_i² / W²) ≤ ½ − 1/(2k)`.

**Formalization Note.** `W = Σ_{i=1}^k w_i` (the printed `Σ_{i=0}^k` is read as `Σ_{i=1}^k`, the
only reading under which the printed chain is an identity). The works `w_i ≥ 0` have positive
total, `k ≥ 1`. -/
theorem waste_bound_4_3 (k : ℕ) (hk : 1 ≤ k) (w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hW : 0 < ∑ i ∈ Finset.Icc 1 k, w i) :
    (∑ i ∈ Finset.Icc 1 k, (1 - (∑ j ∈ Finset.Icc 1 i, w j) / ∑ m ∈ Finset.Icc 1 k, w m) *
        (w i / ∑ m ∈ Finset.Icc 1 k, w m)) =
      (1 / 2) * (1 - (∑ i ∈ Finset.Icc 1 k, w i ^ 2) / (∑ m ∈ Finset.Icc 1 k, w m) ^ 2) ∧
    (1 / 2) * (1 - (∑ i ∈ Finset.Icc 1 k, w i ^ 2) / (∑ m ∈ Finset.Icc 1 k, w m) ^ 2) ≤
      1 / 2 - 1 / (2 * (k : ℝ)) := by sorry

end MaxMinFracSched
