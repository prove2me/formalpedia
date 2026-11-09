-- Prove2me | Theorems.Thm_LocalLLL_Main_lemma_2_2
-- name    : LocalLLL.Main.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:04.112881+00:00
-- url     : https://prove2.me/theorems/a9256aee-c419-4ae4-ad06-84e27f9d6998
-- title:
--   Lemma 2.2 — exponential-criterion LLL
-- statement:
--   There is an absolute constant $C>0$ and an absolute natural exponent $B$ such that, for each desired failure exponent $a>0$, a positive constant $A$ works for all variable LLL instances on at most $n\ge1$ events, of dependency degree at most $d\ge2$, with event probabilities at most $p$ satisfying
--
--   $$p\le2^{-Cd}.$$
--
--   A uniform private-bit LOCAL algorithm solves every such instance in $T\le A\ell(n)^B$ rounds with failure outer measure at most $n^{-a}$. Neither $A$ nor $B$ depends on $d,p$ or the variable spaces. The algorithm is fixed before the network and event data. This result supplies the solver for the repair LLL.
--
--   Differences from the source:
--   - reading: poly(log log n) with any desired constant failure exponent → one polynomial exponent B before the failure exponent; reason: Reading R: §3.3 changes only multiplicative constants with the failure exponent; the evidence and remaining cited-algorithm burden are recorded in MODERATION_NOTES.md
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - generalization: unique identifiers in the usual LOCAL model → arbitrary injective natural identifiers, without a polynomial size bound; reason: random short identifiers can be generated with sufficiently small collision probability; the theorem specializes to bounded identifiers
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: poly(log log n) asymptotic round complexity → T ≤ A·(log log(n+16))^B for every n ≥ 1; reason: padding preserves the asymptotic class and defines the expression positively at small n; n is a common size upper bound
--   - encoding: success probability at least 1−n^(−a) → outer measure of the failure set at most n^(−a); reason: an upper bound on failure remains meaningful without imposing measurability of arbitrary local computation
--   - encoding: arbitrarily large messages to each neighbor → unrestricted broadcast messages and received-message dictionaries indexed by sender ID; reason: a broadcast may contain one entry per recipient; execution still receives only neighbor messages
--   - generalization: the common size bound n is polynomial in the actual network size in the LOCAL model paragraph → any n ≥ 1 with card V ≤ n, including empty networks and arbitrarily loose upper bounds; reason: the source explicitly permits padding by isolated vertices in §2; padding to n and restricting execution to the original components gives the same guarantee and includes every source instance
--   - encoding: each vertex outputs values for its own variable set → each output is a full assignment, with agreement tested only on that vertex’s variable set; reason: irrelevant coordinates carry no correctness requirements; coordinate probability laws ensure nonempty domains, so local assignments extend by choice
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Lemma 2.2, p. 2 (PDF 3); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- Lemma 2.2, printed p. 2; Appendix A.2, p. 17. C precedes the failure exponent. -/
theorem lemma_2_2 :
    ∃ C : ℝ, 0 < C ∧ ∃ B : ℕ, ∀ a : ℝ, 0 < a → ∃ A : ℝ, 0 < A ∧
      ∀ (ι : Type) (α : ι → Type) [∀ z, MeasurableSpace (α z)]
        (μ : ∀ z, Measure (α z)) [∀ z, IsProbabilityMeasure (μ z)],
        ∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, 2 ≤ d → ∀ p : ℝ,
        p ≤ (2 : ℝ) ^ (-C * (d : ℝ)) →
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ alg : LocalAlg (LLLInput ι α) (Assignment α),
          solvesWithin μ n d p a alg T := by sorry

end LocalLLL.Main
