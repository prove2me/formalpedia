-- Prove2me | Theorems.Thm_KnodelPrimeCordial_lemma_2_1
-- name    : KnodelPrimeCordial.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-12T06:04:10.571327+00:00
-- url     : https://prove2.me/theorems/2ca607db-fb22-40a0-9812-c6037365c324
-- title:
--   Lemma 2.1 — $W_{3,8}$ is not prime cordial
-- statement:
--   The Knödel graph $W_{3,8}$ (eight vertices, twelve edges, $3$-regular) is not prime cordial: for every bijection $f$ from its vertex set onto $\{1,\dots,8\}$, the numbers of edges $uv$ with $\gcd(f(u),f(v))=1$ and with $\gcd(f(u),f(v))>1$ differ by at least $2$.
--
--   $$
--   \neg\,\mathrm{PrimeCordial}(W_{3,8}).
--   $$
--
--   This is the single exception in the paper's main theorem.
--
--   Differences from the source:
--   - encoding: vertex (i, j) with i = 1, 2 → Fin 2 × Fin 4 with sides 1, 2 as 0, 1; reason: Lean convention; same graph
--   - encoding: bijection f from V to {1, …, |V|} → f : V → ℕ with Set.BijOn f univ (Icc 1 |V|); reason: Lean convention; same labelings
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.1, p.3 (PDF p.3)

import Mathlib
import Definitions.Def_KnodelPrimeCordial_PrimeCordial
import Definitions.Def_KnodelPrimeCordial_knodel

namespace KnodelPrimeCordial

/-- **Lemma 2.1** (Haque, Khanam, Shahriar, *Prime cordial labeling of Knödel graph*,
manuscript (2026), §2, p.3): "W(3, 8) is not prime cordial."

The Knödel graph `W_{3,8}` (8 vertices, 12 edges) has no prime cordial labeling. -/
theorem lemma_2_1 : ¬ PrimeCordial (knodel 3 8) := by sorry

end KnodelPrimeCordial
