-- Prove2me | Theorems.Thm_MatchVec3_degree_le_fiberMax
-- name    : MatchVec3.degree_le_fiberMax
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:48.208039+00:00
-- url     : https://prove2.me/theorems/d79d3c80-601f-4526-adda-20dc7bd8415a
-- title:
--   Proof of Theorem 5.2: $\Delta(F)\le M_{L-1}(U)$
-- statement:
--   For $L\ge1$, a list $U$ in $\mathbb Z^n_m$ and an $L$-sum fiber $F$ of $U$,
--
--   $$\Delta(F)\le M_{L-1}(U).$$
--
--   The sets of $F$ containing a fixed vertex lie, after removing it, in one $(L-1)$-sum fiber.
--
--   Differences from the source:
--   - generalization: a 3-restricted family modulo a minimal divisor, L > q → any list U over any modulus, L ≥ 1; reason: the argument uses only the sums
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), proof of Theorem 5.2, p.14

import Mathlib
import Definitions.Def_MatchVec3_fiberMax
import Definitions.Def_MatchVec3_maxDegree

namespace MatchVec3

/-- **The degree bound** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256 44199413…), proof
of Theorem 5.2, p.14): the maximum degree of an `L`-sum fiber satisfies `∆(F) ≤ M_{L-1}(U)`.

**Formalization Note** No matching-vector hypothesis is needed. `L - 1` is safe since `1 ≤ L`. -/
theorem degree_le_fiberMax {m n K L : ℕ} (hL : 1 ≤ L) (U : Fin K → Fin n → ZMod m)
    (x : Fin n → ZMod m) :
    maxDegree (fiber U L x) ≤ fiberMax U (L - 1) := by sorry

end MatchVec3
