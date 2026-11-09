-- Prove2me | Theorems.Thm_LocalLLL_Main_theorem_1_1
-- name    : LocalLLL.Main.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:56:22.188069+00:00
-- url     : https://prove2.me/theorems/aeb7f434-db7e-4fed-96a0-551526e83ee5
-- title:
--   Theorem 1.1 — LOCAL LLL in poly(log log n) rounds
-- statement:
--   For an arbitrary family of independent random variables, let at most $n\ge1$ measurable bad events be determined by their given coordinate sets, and let $G$ contain every shared-variable dependency edge. If its maximum degree is at most the integer $d\ge2$, and every event has probability at most a real number $p$ with
--
--   $$p\,d^{1000}<1,$$
--
--   there is a uniform randomized LOCAL algorithm that outputs consistent values avoiding every event. More precisely, there is one absolute natural exponent $B$ such that for every desired $\gamma>0$ a constant $A>0$, independent of $d,p,n$ and all instance data, gives
--
--   $$T\le A\bigl(\log\log(n+16)\bigr)^B,\qquad \Pr[\text{failure}]\le n^{-\gamma}.$$
--
--   The algorithm may use $n,d,p,\gamma$ and the variable laws, but is chosen before the vertex type, graph, identifiers, coordinate sets and events. Its initial input at a node is only that node's coordinate set, event, identifier and private tape. There is no countability, finite-domain or finite-coordinate-set hypothesis. This is the paper's full headline theorem, uniform in degree and event probabilities.
--
--   Differences from the source:
--   - reading: poly(log log n) with any desired constant failure exponent → one polynomial exponent B before the failure exponent; reason: Reading R: §3.3 changes only multiplicative constants with the failure exponent; the evidence and remaining cited-algorithm burden are recorded in MODERATION_NOTES.md
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - generalization: unique identifiers in the usual LOCAL model → arbitrary injective natural identifiers, without a polynomial size bound; reason: random short identifiers can be generated with sufficiently small collision probability; the theorem specializes to bounded identifiers
--   - encoding: poly(log log n) asymptotic round complexity → T ≤ A·(log log(n+16))^B for every n ≥ 1; reason: padding preserves the asymptotic class and defines the expression positively at small n; n is a common size upper bound
--   - encoding: success probability at least 1−n^(−a) → outer measure of the failure set at most n^(−a); reason: an upper bound on failure remains meaningful without imposing measurability of arbitrary local computation
--   - encoding: arbitrarily large messages to each neighbor → unrestricted broadcast messages and received-message dictionaries indexed by sender ID; reason: a broadcast may contain one entry per recipient; execution still receives only neighbor messages
--   - generalization: the common size bound n is polynomial in the actual network size in the LOCAL model paragraph → any n ≥ 1 with card V ≤ n, including empty networks and arbitrarily loose upper bounds; reason: the source explicitly permits padding by isolated vertices in §2; padding to n and restricting execution to the original components gives the same guarantee and includes every source instance
--   - encoding: each vertex outputs values for its own variable set → each output is a full assignment, with agreement tested only on that vertex’s variable set; reason: irrelevant coordinates carry no correctness requirements; coordinate probability laws ensure nonempty domains, so local assignments extend by choice
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Theorem 1.1, p. 1 (PDF 2); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- Theorem 1.1, printed p. 1. Absolute exponent, constants uniform in degree and probabilities;
the algorithm is chosen before every graph, identifier assignment, variable set and event. -/
theorem theorem_1_1 :
    ∃ B : ℕ, ∀ γ : ℝ, 0 < γ → ∃ A : ℝ, 0 < A ∧
      ∀ (ι : Type) (α : ι → Type) [∀ z, MeasurableSpace (α z)]
        (μ : ∀ z, Measure (α z)) [∀ z, IsProbabilityMeasure (μ z)],
        ∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ,
        p * (d : ℝ) ^ (1000 : ℕ) < 1 →
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ alg : LocalAlg (LLLInput ι α) (Assignment α),
          solvesWithin μ n d p γ alg T := by sorry

end LocalLLL.Main
