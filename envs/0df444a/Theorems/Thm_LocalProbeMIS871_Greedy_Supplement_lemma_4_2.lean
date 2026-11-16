-- Prove2me | Theorems.Thm_LocalProbeMIS871_Greedy_Supplement_lemma_4_2
-- name    : LocalProbeMIS871.Greedy.Supplement.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T21:04:15.973461+00:00
-- url     : https://prove2.me/theorems/85b271bf-8603-47e2-8abc-7e8ea498c716
-- title:
--   Lemma 4.2 — Both MIS cardinality bounds and both membership probabilities
-- statement:
--   Use the exact graph experiments $D_0,D_1$ of §4.1, with hidden $A$ of size $N$, and the same $\eta_{c_*}(\Delta,m)$ as Lemma 4.1. For sufficiently large $\Delta$ and then sufficiently large admissible $m$, simultaneously every MIS $I$ of a $D_0$ graph obeys the following cardinality bound outside an event of probability at most $\eta_{c_*}$:
--
--   $$\Pr_{D_0}[\forall I\text{ maximal independent},\ |I\cap A|\ge N/4]\ge1-\eta_{c_*}(\Delta,m).$$
--
--   For every graph in $D_1$, every independent set $I$, without a maximality requirement, satisfies
--
--   $$|I\cap A|\le N/8.$$
--
--   For every zero-error stateless MIS LCA $A$, let $I_A(G,L,r)$ be the set defined by its actual answers on shared tape $r$, independent of the graph experiment, and query $v_i$ uniformly from hidden $A$. Then
--
--   $$\Pr[v_0\in I_A(G_0,L_0,r)]\ge\tfrac14-\eta_{c_*}(\Delta,m),\qquad
--   \Pr[v_1\in I_A(G_1,L_1,r)]\le\tfrac18.$$
--
--   The two $D_1$ assertions hold for every admissible construction size; the $D_0$ assertions have the nested sufficiently-large parameter range of Lemma 4.1. The probabilities average over graph connections, labels, list orders, uniform hidden query and the independent tape. Correctness is simultaneous across roots for each fixed input.
--
--   These four conclusions turn structural constraints on all possible MIS choices into a membership-probability gap for arbitrary algorithms.
--
--   **Formalization Note** Cardinalities are cast to real numbers before division. The numerical error witness is the same $c_*=1/2304$ selected in Lemma 4.1. The $D_1$ clauses are placed first to state their unrestricted admissible-$m$ domain explicitly.
--
--   Differences from the source:
--   - encoding: vertices labeled in [n] → vertices represented by Fin n; reason: adding one to each label is a bijection and preserves all graph and oracle information
--   - encoding: the finite distributions D₀ and D₁ of §4.1 → uniform counting on finite permutation seeds followed by the specified graph, list and query maps; reason: all fibers have constant multiplicity, so these are exactly the source laws, with no conditioning
--   - encoding: an unspecified positive absolute c_* in η → the existential witness c_*=1/2304 from Eq. (40), shared by both lemmas; reason: h≤2N makes (N/12)^2/(8h)≥N/2304; this selects a witness without dropping any instance
--   - encoding: probability over independent graph experiment and tape → a finite uniform average of tape-event probabilities; reason: finite averaging is exactly the independent product law, for arbitrary measurable tape spaces
--   - encoding: an arbitrary input-independent shared tape and its probabilities → an arbitrary probability space with measurable next-action equality events; reason: this is the implicit observational measurability needed for the source probabilities, without restricting the law or access to the tape
-- source:
--   Peter Kiss, Yuichi Yoshida, The Local Probe Complexity of Maximal Independent Set, STOC 2027 submission #871 (October 2026), p. 26, PDF p. 28, Lemma 4.2

import Definitions.Def_LocalProbeMIS871_Greedy_Supplement_Observation

open MeasureTheory
open scoped BigOperators Classical
noncomputable section
set_option autoImplicit false
universe uLemma42

namespace LocalProbeMIS871.Greedy.Supplement

/-- Lemma 4.2, printed p.26 / PDF28. Both structural assertions and both probabilities. -/
theorem lemma_4_2 :
    (∀ (Δ m : ℕ), Admissible Δ m →
      (∀ (s : Seed Δ m) (I : Finset (Fin (graphSize Δ m))),
        Independent (sampleGraph true s) I →
          ((I ∩ sampleA s).card : ℝ) ≤ (aSize Δ m : ℝ) / 8) ∧
      (∀ (Ω : Type uLemma42) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Algorithm Ω), ZeroError μ Δ A →
          membershipProbability μ A true Δ m ≤ (1 / 8 : ℝ))) ∧
    ∃ Δ₀ : ℕ, 2 ≤ Δ₀ ∧ ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ M : ℕ,
      ∀ m : ℕ, M ≤ m → Admissible Δ m →
      (1 - eta cStar Δ m ≤ finiteProb (fun s : Seed Δ m =>
        ∀ I : Finset (Fin (graphSize Δ m)), IsMIS (sampleGraph false s) I →
          (aSize Δ m : ℝ) / 4 ≤ ((I ∩ sampleA s).card : ℝ))) ∧
      (∀ (Ω : Type uLemma42) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
        (A : Algorithm Ω), ZeroError μ Δ A →
          (1 / 4 : ℝ) - eta cStar Δ m ≤ membershipProbability μ A false Δ m) := by sorry

end LocalProbeMIS871.Greedy.Supplement
