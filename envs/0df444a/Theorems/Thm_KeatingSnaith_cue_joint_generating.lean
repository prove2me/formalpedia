-- Prove2me | Theorems.Thm_KeatingSnaith_cue_joint_generating
-- name    : KeatingSnaith.cue_joint_generating
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T12:51:35.192916+00:00
-- url     : https://prove2.me/theorems/19f5c1db-6641-47e0-b642-c30083625913
-- title:
--   Joint generating function $\langle|Z|^{t}e^{is\,\mathrm{Im}\log Z}\rangle_{CUE}$
-- statement:
--   This is the **joint generating function** of the real and imaginary parts of $\log Z$, the formula from which the mission's goal is derived.
--
--   Let $N\ge 1$ and let $t,s$ be real numbers with
--
--   1. $t>-1$,
--   2. $\tfrac{t}{2}+\tfrac{s}{2}>-1$,
--   3. $\tfrac{t}{2}-\tfrac{s}{2}>-1$.
--
--   Then
--
--   $$
--   \bigl\langle |Z|^{t}\,e^{\,i s\operatorname{Im}\log Z}\bigr\rangle_{\mathrm{CUE}(N)} \;=\; \prod_{j=1}^{N}\frac{\Gamma(j)\,\Gamma(t+j)}{\Gamma\!\left(j+\tfrac{t}{2}+\tfrac{s}{2}\right)\,\Gamma\!\left(j+\tfrac{t}{2}-\tfrac{s}{2}\right)} .
--   $$
--
--   Setting $s=0$ recovers the moment formula for $|Z|$ and setting $t=0$ recovers the characteristic function of $\operatorname{Im}\log Z$, so this single identity contains both one-variable generating functions. Its role in the chapter is to supply the *joint* cumulants of $(\log|Z|,\operatorname{Im}\log Z)$, which is how the asymptotic independence of the two parts is established.
-- source:
--   N. C. Snaith, Random Matrix Theory and zeta functions, PhD thesis, University of Bristol, June 2000, Chapter 2, p. 56, eq. (2.6.7) with the validity conditions Re t/2 + Re s/2 > -1, Re t/2 - Re s/2 > -1, Re t > -1 stated immediately below it

import Definitions.Def_keating_snaith_cue

namespace KeatingSnaith

open Finset MeasureTheory Filter Topology
open scoped Real

/-- The joint generating function of `log |Z|` and `Im log Z` (thesis eq. (2.6.7)). -/
theorem cue_joint_generating (N : ℕ) (hN : 1 ≤ N) (t s : ℝ) (ht : -1 < t)
    (hts : -1 < t / 2 + s / 2) (hts' : -1 < t / 2 - s / 2) :
    cueAverage N (fun θ =>
        ((‖charPoly N θ‖ ^ t : ℝ) : ℂ) * Complex.exp (s * imLogZ N θ * Complex.I))
      = ((∏ j ∈ Finset.range N,
            Real.Gamma (j + 1) * Real.Gamma (t + j + 1) /
              (Real.Gamma (j + 1 + t / 2 + s / 2) *
                Real.Gamma (j + 1 + t / 2 - s / 2)) : ℝ) : ℂ) := by
  sorry

end KeatingSnaith
