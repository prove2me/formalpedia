-- Prove2me | Theorems.Thm_NonuniformCompetitive_Snoopy_Supplement_theorem_14
-- name    : NonuniformCompetitive.Snoopy.Supplement.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:08:26.206451+00:00
-- url     : https://prove2.me/theorems/739f2adb-896b-4127-99a1-5b1e75d631dd
-- title:
--   Theorem 14 — the collinear 1–1–2 triangle has exact ratio 3/2
-- statement:
--   Let a metric space consist of exactly three points $a,b,d$ with $d(a,b)=d(b,d)=1$ and $d(a,d)=2$. From every initial two-server configuration $s_0$,
--   $$\bigl(\forall A,c:\ A\text{ is }c\text{-competitive from }s_0\Rightarrow c\ge3/2\bigr)
--   \quad\text{and}\quad
--   \exists A:\ A\text{ is }(3/2)\text{-competitive from }s_0.$$
--   Algorithms are randomized causal server algorithms, and the adversary is oblivious. Both clauses retain an additive constant independent of the finite request sequence.
--
--   The entire three-point metric and both optimality claims are included, without restricting the request sequence to a phase family.
--
--   Differences from the source:
--   - encoding: a triangle with integer edge lengths 1, 1, 2 → a metric type exhausted by a,b,d with the three exact distance equalities; reason: the equalities imply distinctness and specify the complete metric, with no request-time restriction
--   - reading: the display omits the adversary phrase → the oblivious mixed-strategy comparison from the published KServer model; reason: this is the standing adversary convention of §5
--   - encoding: lower bound and attainment at 3/2 → their conjunction for every initial labelled configuration; reason: labels are bookkeeping for actual server paths; the additive constant absorbs any fixed initial repositioning
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 568, Theorem 14 and governing context

import Mathlib
import Definitions.Def_KServer_randomized

namespace NonuniformCompetitive.Snoopy.Supplement

/-- Theorem 14, pp.568–569: the whole three-point collinear metric, with
arbitrary finite request words and arbitrary initial configurations. The adversary
is oblivious by the standing convention of §5. Both optimality clauses are retained. -/
theorem theorem_14 {M : Type} [MetricSpace M]
    (a b d : M) (hab : dist a b = 1) (hbd : dist b d = 1) (had : dist a d = 2)
    (hM : ∀ x : M, x = a ∨ x = b ∨ x = d) (s₀ : KServer.Config 2 M) :
    (∀ (A : KServer.RandomizedAlgorithm 2 M) (c : ℝ),
      A.IsCompetitiveFrom s₀ c → (3 / 2 : ℝ) ≤ c) ∧
    (∃ A : KServer.RandomizedAlgorithm 2 M, A.IsCompetitiveFrom s₀ (3 / 2 : ℝ)) := by sorry

end NonuniformCompetitive.Snoopy.Supplement
