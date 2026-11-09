-- Prove2me | Theorems.Thm_IntervalMaxCutEPTAS_Scheme_eq_3
-- name    : IntervalMaxCutEPTAS.Scheme.eq_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:16:28.15392+00:00
-- url     : https://prove2.me/theorems/283417ef-20d1-4dda-bd63-78eacdd6ef4a
-- title:
--   (3) — mc(G) ≥ m/2, and mb(G) ≥ m/2 when n ≥ 2
-- statement:
--   Let $G$ be a finite simple graph with $n$ vertices and $m$ edges. Then
--
--   $$\mathrm{mc}(G)\ge \frac m2\qquad\text{and}\qquad \mathrm{mb}(G)\ge\frac m2\ \text{ if } n\ge 2.$$
--
--   These lower bounds turn the additive losses of the approximation scheme (multiples of $\varepsilon m$) into multiplicative ones.
--
--   Differences from the source:
--   - encoding: mc(G) ≥ m/2 and mb(G) ≥ m/2 → m ≤ 2·mc(G) and m ≤ 2·mb(G) in ℕ; reason: exact equivalence for natural numbers
-- source:
--   Morteza Alimi, Hani Ahmadzadeh, STOC 2027 submission #636 (October 2026), §3, display (3), PDF p. 14 (printed p. 13)

import Mathlib
import Definitions.Def_IntervalMaxCutEPTAS_Scheme_Graph

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace IntervalMaxCutEPTAS.Scheme

/-- (3), §3: `mc(G) ≥ m/2`, and `mb(G) ≥ m/2` if `n ≥ 2`, for every finite simple graph. -/
theorem eq_3 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card ≤ 2 * mc G ∧
      (2 ≤ Fintype.card V → G.edgeFinset.card ≤ 2 * mb G) := by sorry

end IntervalMaxCutEPTAS.Scheme
