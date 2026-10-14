-- Prove2me | Theorems.Thm_IntMul_HvdH_convC_round
-- name    : IntMul.HvdH.convC_round
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T04:12:03.98504+00:00
-- url     : https://prove2.me/theorems/0204cd0f-5a00-43b8-8e22-b0a4a1d22317
-- title:
--   One rounding after an exact convolution
-- statement:
--   Let $t_i=2^{e_i}$ for $i<d$, $r\ge1$ and $T=r\prod_it_i$. Let $U,V$ be Gaussian-integer arrays on the box $t_1\times\cdots\times t_d\times r$ with $|U_x|,|V_x|\le2^p$ on the box. Let $W_j$ be the exact unnormalised cyclic convolution at an index $j$, i.e. $W_j=\sum_{k,c}U_{(k,c)}V_{(j-k,\,j_{d+1}-c)}$ with indices taken cyclically. Dividing both parts of $W_j$ by $2^pT$ with rounding towards zero gives $\widetilde W_j$, which satisfies
--   $$|\widetilde W_j|\le2^p,\qquad\bigl|\widetilde W_j-2^p\,\tfrac1T(u*v)_j\bigr|\le\sqrt2,$$
--   where $u=2^{-p}U$, $v=2^{-p}V$ and $\frac1T(u*v)$ is `convC`. So any exact integer convolution routine followed by one rounding meets the oracle hypothesis of `bluestein_fp` with $\delta=\sqrt2$.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, §3 (variant with exact convolution)

import Definitions.Def_IntMul_HvdH_ConvC

namespace IntMul.HvdH
theorem convC_round {d : ℕ} (p r : ℕ) (e : Fin d → ℕ) (hr : 0 < r)
    (U V W : (Fin (d + 1) → ℕ) → ℤ × ℤ)
    (hU : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (U x)‖ ≤ 2 ^ p)
    (hV : ∀ x : Fin (d + 1) → ℕ, (∀ i : Fin d, x i.castSucc < 2 ^ e i) → x (Fin.last d) < r →
      ‖gC (V x)‖ ≤ 2 ^ p)
    (j : Fin (d + 1) → ℕ)
    (hW : gC (W j) = ∑ k ∈ Fintype.piFinset (fun i : Fin d => Finset.range (2 ^ e i)),
      ∑ c ∈ Finset.range r, gC (U (Fin.snoc (fun i => k i) c)) *
        gC (V (Fin.snoc (fun i => (j i.castSucc + 2 ^ e i - k i) % 2 ^ e i)
          ((j (Fin.last d) + r - c) % r)))) :
    ‖gC ((W j).1.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ),
        (W j).2.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ))‖ ≤ 2 ^ p ∧
    ‖gC ((W j).1.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ),
        (W j).2.tdiv ((2 ^ p * (r * 2 ^ (∑ i, e i)) : ℕ) : ℤ)) -
      2 ^ p * convC r e (fun x => gC (U x) / 2 ^ p) (fun x => gC (V x) / 2 ^ p) j‖ ≤
      Real.sqrt 2 := by sorry
end IntMul.HvdH
