-- Prove2me | Theorems.Thm_KnodelPrimeCordial_lemma_2_3
-- name    : KnodelPrimeCordial.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:04:18.866371+00:00
-- url     : https://prove2.me/theorems/be27a6d0-01d1-46f0-b9ba-0d15398f9cfb
-- title:
--   Lemma 2.3 — $W_{3,n}$ is prime cordial for every even $n\ge 10$
-- statement:
--   For every even $n\ge 10$, the Knödel graph $W_{3,n}$ is prime cordial: there is a bijection $f$ from its vertex set onto $\{1,\dots,n\}$ such that the numbers of edges $uv$ with $\gcd(f(u),f(v))=1$ and with $\gcd(f(u),f(v))>1$ differ by at most one.
--
--   $$
--   \mathrm{PrimeCordial}(W_{3,n})\qquad(n\text{ even},\ n\ge 10).
--   $$
--
--   Together with Lemma 2.1 this gives the main theorem.
--
--   Differences from the source:
--   - encoding: n ≥ 10 (W(3, n) is defined for even n) → hypotheses Even n and 10 ≤ n; reason: the definition's domain stated as a binder
--   - encoding: vertex (i, j) with i = 1, 2 → Fin 2 × Fin (n/2) with sides 1, 2 as 0, 1; reason: Lean convention; same graph
--   - encoding: bijection f from V to {1, …, |V|} → f : V → ℕ with Set.BijOn f univ (Icc 1 |V|); reason: Lean convention; same labelings
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

namespace KnodelPrimeCordial

/-- **Lemma 2.3** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel graph*,
manuscript (2026), §2, p.3; proof pp.4–6): "W(3, n) is prime cordial for n ≥ 10."

For every even `n ≥ 10`, the Knödel graph `W_{3,n}` has a prime cordial labeling.

**Formalization Note** `W_{3,n}` is defined only for even `n`, so "n ≥ 10" is
`Even n ∧ 10 ≤ n`. -/
theorem lemma_2_3 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) : PrimeCordial (knodel 3 n) := by sorry

end KnodelPrimeCordial
