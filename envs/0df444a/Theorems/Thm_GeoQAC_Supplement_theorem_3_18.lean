-- Prove2me | Theorems.Thm_GeoQAC_Supplement_theorem_3_18
-- name    : GeoQAC.Supplement.theorem_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T05:23:34.089994+00:00
-- url     : https://prove2.me/theorems/664a1d03-a3e4-4afe-bd62-b6cfbafdc5d4
-- title:
--   Theorem 3.18 — average sensitivity of $\mathrm{MOD}_{r,n}$ and the MOD width bound
-- statement:
--   1. For every fixed modulus $r\ge3$,
--   $$
--   \lim_{n\to\infty}\frac{\mathrm{as}(\mathrm{MOD}_{r,n})}{n}=\frac2r ,
--   $$
--   that is, $\mathrm{as}(\mathrm{MOD}_{r,n})=(2/r+o(1))\,n$.
--   2. There is an absolute constant $c>0$ such that for every $r\ge3$ and every depth $d\ge1$ there is $N$ with: for all $n\ge N$, every depth-$d$ $[w,h]$-2D-QAC circuit computing $\mathrm{MOD}_{r,n}$ exactly from product ancillas (inputs and output anywhere) has
--   $$
--   c\left(\frac{n}{r^2}\right)^{1/(6d+1)}\le w .
--   $$
--
--   The modular counting functions have linear average sensitivity and so need polynomial width at every fixed depth.
--
--   Differences from the source:
--   - reading: w = Ω((n/r²)^{1/(6d+1)}) for fixed d with an absolute implicit constant → one absolute c for all r ≥ 3 and d ≥ 1, the bound holding for n ≥ N(r, d); reason: asymptotic notation in n for fixed r, d; the proof needs n large in terms of r (as(MOD_{r,n}) ≥ n/r for sufficiently large n, p.27)
--   - encoding: product ancillas (§3.5) → any product of one-qubit unit vectors (published GeoQAC.ComputesExactly); reason: the paper's own convention for §3.5; |0^a⟩ is the special case
-- source:
--   Dong, Ou, Yao, On the Computational Power of Geometrically Local QAC circuits, arXiv:2604.07178 (version of 2026-11-03), Theorem 3.18, p.26

import Mathlib
import Definitions.Def_GeoQAC_QACCircuit_Is2D
import Definitions.Def_GeoQAC_ComputesExactly
import Definitions.Def_GeoQAC_avgSens
import Definitions.Def_GeoQAC_Supplement_hammingWeight

namespace GeoQAC.Supplement

open GeoQAC

/-- **Theorem 3.18** (Dong, Ou, Yao, arXiv:2604.07178, version of 2026-11-03, p.26). "For every fixed
`r ≥ 3`, `as(MOD_{r,n}) = (2/r + o(1)) · n`. For fixed depth `d ≥ 1`, exact computation of
`MOD_{r,n}` requires `w = Ω((n/r²)^{1/(6d+1)})`. The implicit constant is absolute."

**Formalization Note.**
* First clause: `as(MOD_{r,n})/n → 2/r` as `n → ∞`, for every `r ≥ 3` (the `o(1)` is in `n`, `r`
  fixed).
* Second clause: one absolute constant `c > 0` for all `r ≥ 3` and `d ≥ 1`; the threshold `N` beyond
  which the bound holds may depend on the fixed `r` and `d` (asymptotic notation in `n`).
* Exact computation from product ancillas (§3.5, p.26) is the published `GeoQAC.ComputesExactly`
  (inputs anywhere, output anywhere, garbage allowed). Real exponent `1/(6d+1)`. -/
theorem theorem_3_18 :
    (∀ r : ℕ, 3 ≤ r →
      Filter.Tendsto (fun n : ℕ => avgSens (modFn r n) / n) Filter.atTop
        (nhds (2 / (r : ℝ)))) ∧
    (∃ c : ℝ, 0 < c ∧ ∀ r d : ℕ, 3 ≤ r → 1 ≤ d → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ (w h : ℕ) (C : QACCircuit (Pos w h) d) (inp : Fin n ↪ Pos w h)
        (anc : Pos w h → Bool → ℂ) (out : Pos w h),
        C.Is2D → ComputesExactly C inp anc out (modFn r n) →
          c * ((n : ℝ) / (r : ℝ) ^ 2) ^ ((1 : ℝ) / (6 * (d : ℝ) + 1)) ≤ w) := by sorry

end GeoQAC.Supplement
