-- Prove2me | Theorems.Thm_LocalLLL_Main_section_3_3_constant_degree
-- name    : LocalLLL.Main.section_3_3_constant_degree
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:17.721089+00:00
-- url     : https://prove2.me/theorems/bf3d0634-0791-44f7-80cc-aaa7a2e6dcb5
-- title:
--   §3.3 — constant-degree case
-- statement:
--   For every fixed natural degree cap $D$, there is a natural exponent $B$ such that for each $a>0$ some positive constant $A$ works for all finite variable LLL instances on at most $n\ge1$ events whose dependency degree bound satisfies $2\le d\le D$ and whose event probabilities are at most $p$ with
--
--   $$p(ed)^{32}<1.$$
--
--   A uniform LOCAL algorithm solves every such instance in $T\le A\ell(n)^B$ rounds, with failure outer measure at most $n^{-a}$. The constants may depend on $D$ but not the individual instance or its chosen degree bound. This is the cited constant-degree ingredient in §3.3, keeping its original criterion.
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
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.3 constant-degree paragraph, p. 7 (PDF 8); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- §3.3 constant-degree case, printed p. 7, cited criterion p(ed)^32 < 1. -/
theorem section_3_3_constant_degree :
    ∀ D : ℕ, ∃ B : ℕ, ∀ a : ℝ, 0 < a → ∃ A : ℝ, 0 < A ∧
      ∀ (ι : Type) (α : ι → Type) [∀ z, MeasurableSpace (α z)]
        (μ : ∀ z, Measure (α z)) [∀ z, IsProbabilityMeasure (μ z)],
        ∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ,
        d ≤ D → p * (Real.exp 1 * (d : ℝ)) ^ (32 : ℕ) < 1 →
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ alg : LocalAlg (LLLInput ι α) (Assignment α),
          solvesWithin μ n d p a alg T := by sorry

end LocalLLL.Main
