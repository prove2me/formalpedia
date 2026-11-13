-- Prove2me | Theorems.Thm_KnodelPrimeCordial_theorem_2_4_prime_cordial_iff
-- name    : KnodelPrimeCordial.theorem_2_4_prime_cordial_iff
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:04:29.061197+00:00
-- url     : https://prove2.me/theorems/f6e85d40-0cf5-4a0b-af67-a1e2ac103237
-- title:
--   Theorem 2.4 — $W_{3,n}$ is prime cordial if and only if $n\ne 8$
-- statement:
--   For every even $n\ge 8$ (the range on which the Knödel graph $W_{3,n}$ is defined, since $3\le\lfloor\log_2 n\rfloor$),
--
--   $$
--   W_{3,n}\ \text{is prime cordial}\iff n\ne 8 .
--   $$
--
--   That is, every $W_{3,n}$ with $n\ge 10$ admits a bijection $f$ onto $\{1,\dots,n\}$ whose numbers of edges with coprime and with non-coprime end labels differ by at most one, and $W_{3,8}$ admits none. This is the paper's main result ("$W(3,n)$ is prime cordial for all $n$ except $W(3,8)$"); both the positive clause and the exception are part of the statement.
--
--   Differences from the source:
--   - encoding: all n (W(3, n) is defined for even n with 3 ≤ ⌊log₂ n⌋) → hypotheses Even n and 8 ≤ n; reason: the definition's domain stated as binders
--   - encoding: vertex (i, j) with i = 1, 2 → Fin 2 × Fin (n/2) with sides 1, 2 as 0, 1; reason: Lean convention; same graph
--   - encoding: bijection f from V to {1, …, |V|} → f : V → ℕ with Set.BijOn f univ (Icc 1 |V|); reason: Lean convention; same labelings
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Theorem 2.4, p.6 (PDF p.6); abstract, p.1

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

namespace KnodelPrimeCordial

/-- **Theorem 2.4** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel graph*,
manuscript (2026), §2, p.6; abstract, p.1): "W(3, n) is prime cordial for all n except
W(3, 8)."

For every even `n ≥ 8` (the range on which `W_{3,n}` is defined, `3 ≤ ⌊log₂ n⌋`), the Knödel
graph `W_{3,n}` is prime cordial if and only if `n ≠ 8`.

**Formalization Note** "All n" is the definition's domain, `Even n ∧ 8 ≤ n`. The "except"
clause is part of the statement: `W_{3,8}` is not prime cordial. -/
theorem theorem_2_4_prime_cordial_iff (n : ℕ) (hn : Even n) (h8 : 8 ≤ n) :
    PrimeCordial (knodel 3 n) ↔ n ≠ 8 := by sorry

end KnodelPrimeCordial
