-- Prove2me | Theorems.Thm_MatchVec3_theorem_1_2
-- name    : MatchVec3.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:32.489208+00:00
-- url     : https://prove2.me/theorems/774a9db8-83d3-434c-990f-40e90584ef80
-- title:
--   Theorem 1.2: $MV(m,n,3)\le\exp(C_m\sqrt{n\log n})$
-- statement:
--   **Main theorem.** For every integer $m\ge2$ there is a constant $C_m$ such that for all $n\ge2$,
--
--   $$MV(m,n,3)\le\exp\big(C_m\sqrt{n\log n}\big).$$
--
--   Here $MV(m,n,3)$ is the largest size of a 3-restricted matching vector family in $\mathbb Z^n_m$, and $\log$ is natural. The previous bound for fixed $m$ was $\exp(O_m(n/\log n))$. Since a 3-restricted family of size $K$ gives a 3-query matching-vector code of message length $K$ and codeword length $m^n$, the theorem bounds such codes from below.
--
--   Differences from the source:
--   - encoding: "a constant C_m" → ∃ C > 0, after m and before n; reason: a larger constant still works, as the square root is nonnegative
--   - encoding: "the largest size" → sSup on ℕ; reason: the set is nonempty and bounded by m^n for m ≥ 1, so it is the maximum
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Theorem 1.2, p.3

import Mathlib
import Definitions.Def_MatchVec3_MV

namespace MatchVec3

/-- **Theorem 1.2 (Main theorem)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Theorem 1.2, p.3): for every fixed integer `m ≥ 2` there is a constant `C_m` such that
`MV(m, n, 3) ≤ exp(C_m √(n log n))` for all `n ≥ 2`.

**Formalization Note** `C` comes after `m` and before `n`. Taking `C > 0` loses nothing, since a larger
constant still works. `log` is natural. -/
theorem theorem_1_2 : ∀ m : ℕ, 2 ≤ m → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n →
    (MV m n 3 : ℝ) ≤ Real.exp (C * Real.sqrt (n * Real.log n)) := by sorry

end MatchVec3
