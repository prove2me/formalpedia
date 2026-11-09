-- Prove2me | Theorems.Thm_FourBlockIP350_Main_simplex_midpoints
-- name    : FourBlockIP350.Main.simplex_midpoints
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:33:15.614319+00:00
-- url     : https://prove2.me/theorems/cc4b6d18-05e4-4668-90db-68d60002b770
-- title:
--   Claim 4.2.1 — Midpoints in dilated lattice simplices
-- statement:
--   Let $k\ge1$, $0\le r\le k$, and let $p_0,\ldots,p_r\in\mathbb Z^k$ be affinely independent. In the simplex
--   $$P=\operatorname{conv}\{kp_0,\ldots,kp_r\},$$
--   every integer point $w$ that is not one of the vertices has two distinct integer witnesses $u,v\in P$ with $u+v=2w$.
--
--   The claim includes lower-dimensional simplices; for $r=0$ there is no nonvertex and the implication is vacuous as in the source.
--
--   Differences from the source:
--   - encoding: w=(u+v)/2 → u+v=2w over integer vectors; reason: this avoids truncated integer division and is exactly the integral-midpoint condition
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 10, Claim 4.2.1

import Mathlib
import Definitions.Def_FourBlockIP350_Main_LatticeConvexity

namespace FourBlockIP350.Main

open scoped BigOperators

theorem simplex_midpoints {k r : ℕ} (hk : 0 < k) (hr : r ≤ k)
    (p : Fin (r+1) → ZVec k) (hp : IndependentPoints p)
    (w : ZVec k) (hw : realVec w ∈ DilatedSimplex p)
    (hnonvertex : ∀ i, w ≠ (k : ℤ) • p i) :
    ∃ u v : ZVec k, realVec u ∈ DilatedSimplex p ∧ realVec v ∈ DilatedSimplex p ∧
      u ≠ v ∧ u + v = (2 : ℤ) • w := by sorry

end FourBlockIP350.Main
