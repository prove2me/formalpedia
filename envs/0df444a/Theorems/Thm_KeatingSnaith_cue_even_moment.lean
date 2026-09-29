-- Prove2me | Theorems.Thm_KeatingSnaith_cue_even_moment
-- name    : KeatingSnaith.cue_even_moment
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:52:32.790142+00:00
-- url     : https://prove2.me/theorems/7ff6e8d5-afb2-4bb7-acd8-de15300b8ab2
-- title:
--   Even integer moments $\langle|Z|^{2k}\rangle_{CUE}=\prod_{j=1}^{N}\frac{(j-1)!\,(2k+j-1)!}{((j+k-1)!)^2}$
-- statement:
--   The **even integer moments** of $|Z|$ have a purely factorial closed form.
--
--   Let $N\ge 1$ and let $k$ be a non-negative integer. Then
--
--   $$
--   \bigl\langle |Z|^{2k}\bigr\rangle_{\mathrm{CUE}(N)} \;=\; \prod_{j=1}^{N}\frac{(j-1)!\,\bigl(2k+j-1\bigr)!}{\bigl((j+k-1)!\bigr)^{2}} ,
--   $$
--
--   which in the shifted indexing used in the formal statement reads $\prod_{j=0}^{N-1} j!\,(2k+j)!/\bigl((j+k)!\bigr)^2$.
--
--   This is the case $s=2k$ of the moment formula, with every Gamma value collapsing to a factorial. It is the quantity compared with the $2k$-th moment of $|\zeta(1/2+it)|$ in the following chapter of the source, and its first two cases, $\langle|Z|^2\rangle = N+1$ and $\langle|Z|^4\rangle$, correspond to the two moments of $\zeta$ that are classically known.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 60, eq. (2.7.1), first equality

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- The even integer moments of `|Z|` (thesis eq. (2.7.1), first equality). -/
theorem cue_even_moment (N k : ℕ) (hN : 1 ≤ N) :
    cueAverage N (fun θ => ‖charPoly N θ‖ ^ (2 * k))
      = ∏ j ∈ Finset.range N,
          (Nat.factorial j : ℝ) * (Nat.factorial (2 * k + j) : ℝ) /
            (Nat.factorial (j + k) : ℝ) ^ 2 := by
  sorry

end KeatingSnaith
