-- Prove2me | Theorems.Thm_LocalLLL_Main_lemma_3_1
-- name    : LocalLLL.Main.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:09.523422+00:00
-- url     : https://prove2.me/theorems/3d791f93-373f-45c1-aacb-887a5a20dead
-- title:
--   Lemma 3.1 — LLL exponent amplification
-- statement:
--   There are an absolute integer $d_{\min}\ge3$ and an absolute natural exponent $B$ such that for each $a>0$ a positive constant $A$ has the following property. For all $n\ge1$, $d\ge d_{\min}$ and real $1000\le\lambda\le a\log n$, a finite variable LLL of degree at most $d$ and event probabilities at most $d^{-\lambda}$ admits a deterministic 20-round LOCAL construction of the specified amplified labels $(\bigcup_{u\in B_G(v,11)}V_u,F_v)$. The resulting instance has
--
--   $$G'=G^{23},\qquad d'=d^{23},\qquad p'=(d^{23})^{-\lambda^2/700}=d^{-23\lambda^2/700}.$$
--
--   There is also a uniform transformation algorithm with $T\le A\ell(n)^B$ such that, for every fixed assignment $x$ avoiding all $F_v$, it returns a consistent solution of the original instance with failure outer measure at most $n^{-a}$. The algorithms precede the instance and $x$. Each transformation input contains $x$ only restricted to that node's amplified variable set. This is the reduction needed at every recursive level.
--
--   Differences from the source:
--   - reading: poly(log log n) with any desired constant failure exponent → one polynomial exponent B before the failure exponent; reason: Reading R: §3.3 changes only multiplicative constants with the failure exponent; the evidence and remaining cited-algorithm burden are recorded in MODERATION_NOTES.md
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: real λ, natural k=⌊λ/16⌋, and retracted marginals → natural floor, real powers, and splice sections integrated against the original product law; reason: λ≥1000 and d≥3 exclude degenerate floors and powers; no conditioning on a null event is introduced
--   - generalization: unique identifiers in the usual LOCAL model → arbitrary injective natural identifiers, without a polynomial size bound; reason: random short identifiers can be generated with sufficiently small collision probability; the theorem specializes to bounded identifiers
--   - encoding: poly(log log n) asymptotic round complexity → T ≤ A·(log log(n+16))^B for every n ≥ 1; reason: padding preserves the asymptotic class and defines the expression positively at small n; n is a common size upper bound
--   - encoding: success probability at least 1−n^(−a) → outer measure of the failure set at most n^(−a); reason: an upper bound on failure remains meaningful without imposing measurability of arbitrary local computation
--   - encoding: arbitrarily large messages to each neighbor → unrestricted broadcast messages and received-message dictionaries indexed by sender ID; reason: a broadcast may contain one entry per recipient; execution still receives only neighbor messages
--   - encoding: O(1)-round construction and any satisfying assignment as transformation input → 20 rounds, with the supplied assignment restricted to each amplified variable set; reason: radius 20 is specified in Part II on p. 5; local restriction prevents access to distant assignment data
--   - encoding: λ ≤ a log n without an indicated logarithm base → natural logarithm; reason: the parameter a ranges over all positive reals and absorbs the change of base
--   - generalization: the common size bound n is polynomial in the actual network size in the LOCAL model paragraph → any n ≥ 1 with card V ≤ n, including empty networks and arbitrarily loose upper bounds; reason: the source explicitly permits padding by isolated vertices in §2; padding to n and restricting execution to the original components gives the same guarantee and includes every source instance
--   - encoding: each vertex outputs values for its own variable set → each output is a full assignment, with agreement tested only on that vertex’s variable set; reason: irrelevant coordinates carry no correctness requirements; coordinate probability laws ensure nonempty domains, so local assignments extend by choice
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Lemma 3.1, p. 3 (PDF 4); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- Lemma 3.1, printed p. 3; construction radius 20 on p. 5, transformation pp. 6–7. -/
theorem lemma_3_1 :
    ∃ dmin : ℕ, 3 ≤ dmin ∧ ∃ B : ℕ,
      ∀ a : ℝ, 0 < a → ∃ A : ℝ, 0 < A ∧
      ∀ (ι : Type) (α : ι → Type) [∀ z, MeasurableSpace (α z)]
        (μ : ∀ z, Measure (α z)) [∀ z, IsProbabilityMeasure (μ z)],
        ∀ n : ℕ, 1 ≤ n → ∀ d : ℕ, dmin ≤ d → ∀ lam : ℝ,
        1000 ≤ lam → lam ≤ a * Real.log (n : ℝ) →
        ∃ construct : LocalAlg (LLLInput ι α) (LLLInput ι α),
        ∃ T : ℕ, (T : ℝ) ≤ A * loglog n ^ B ∧
        ∃ transform : LocalAlg (TransformInput ι α) (Assignment α),
        ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (id : V → ℕ)
          (vars : V → Set ι) (events : V → Set (Assignment α)),
          Function.Injective id → Fintype.card V ≤ n →
          variableInstance μ G vars events d ((d : ℝ) ^ (-lam)) →
          (∀ ω v, run construct 20 G id (labels vars events) ω v =
            (amplifiedVars G vars v, amplifiedEvent μ G vars events d lam v)) ∧
          variableInstance μ (graphPower G 23) (amplifiedVars G vars)
            (amplifiedEvent μ G vars events d lam) (d ^ 23)
            (((d : ℝ) ^ (23 : ℕ)) ^ (-(lam ^ 2 / 700))) ∧
          (((d : ℝ) ^ (23 : ℕ)) ^ (-(lam ^ 2 / 700))) =
            (d : ℝ) ^ (-23 * lam ^ 2 / 700) ∧
          (∀ x : Assignment α, boundedDanger μ G vars events d lam x →
            tapes V {ω | ¬ Solved vars events
              (run transform T G id (transformLabels G vars events x) ω)} ≤
                ENNReal.ofReal ((n : ℝ) ^ (-a))) := by sorry

end LocalLLL.Main
