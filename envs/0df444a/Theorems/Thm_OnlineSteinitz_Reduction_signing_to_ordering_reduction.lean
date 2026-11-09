-- Prove2me | Theorems.Thm_OnlineSteinitz_Reduction_signing_to_ordering_reduction
-- name    : OnlineSteinitz.Reduction.signing_to_ordering_reduction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:52:49.434595+00:00
-- url     : https://prove2.me/theorems/463dd137-45fb-4943-a130-b066d9dc3ead
-- title:
--   Theorem 2.1 — signing-to-ordering reduction (complete)
-- statement:
--   Algorithm 1 assigns each arriving vector immediately and irrevocably to an unused output slot, without knowing the input total. For each fixed tape it is causal, and at completion its permutation satisfies $\pi(p_t)=t$. Every internal node receives exactly its capacity many vectors and fills its left quota exactly.
--
--   (i) In any fixed norm, suppose $\|v_t\|\le1$. If the proposed terminal signed vector and count at every internal node satisfy $\|\sum_i\varepsilon_i x_i\|\le V(m)$ and $|\sum_i\varepsilon_i|\le W(m)$, then simultaneously for every $0\le k\le T$,
--   $$\|\operatorname{res}_k(v_\pi)\|\le\sum_{u\in P(k)}\left(\frac{V(m_u)+W(m_u)}2+\mathbf1_{\{m_u\text{ odd}\}}\right).$$
--   If the local bounds hold for every stream, this is a deterministic guarantee against adaptive inputs. If for each fixed local length-$m$ unit-ball stream they hold jointly with probability at least $1-p(m)$, then on every oblivious input the same inequality holds for all prefixes on one event of probability at least $1-\sum_{u\text{ internal}}p(m_u)$. This lower bound remains asserted when it is negative.
--
--   (ii) There exists an absolute constant $C>0$, chosen before every instance parameter, such that for every positive dimension $d$, horizon $T\ge1$, common eligible scale $\Sigma\ge1$, fixed Euclidean unit-ball stream and $0<\delta<1$, Algorithm 1 with independent copies of signers on $(x_i,1)/\sqrt2$ satisfies
--   $$\mathbb P\left(\operatorname{res}_{\max}(v_\pi)\le C\Sigma\left(\log T+\sqrt{\log T\,[d+\log(1/\delta)]}\right)\right)\ge1-\delta.$$
--   Both parts use only terminal local guarantees. Totals may be nonzero and are not routing inputs. When the input total is zero, residuals are the ordinary prefix sums. At $T=1$, every residual vanishes.
--
--   This is the complete algorithmic reduction, including both norm/count and subgaussian interfaces, rather than an application to one particular signer.
--
--   Differences from the source:
--   - encoding: positions and arrivals indexed from 1 → zero-based slots and arrivals, with half-open intervals [a,a+m); reason: subtracting one from indices preserves every input and prefix, including k=0,T; values outside the first T slots are ignored
--   - encoding: persistent signer state updated with proposed signs and supplied routing statistics → a tape-dependent function of the current vector and the local vector/proposed-sign history; reason: the capacity is known and quota repair reconstructs all child counts, sums and remaining capacities from this history; state can be replayed without consulting future vectors or descendant tapes
--   - encoding: independent private tapes at the internal nodes → a finite product probability law on an interval grid, with arbitrary measurable tape carrier and node-specific marginal laws; reason: unused coordinates are dummy independent tapes; the router reads only visited nodes, while ancestor conditioning retains the complete tapes
--   - generalization: an arbitrary fixed norm on real finite-dimensional vector space → an arbitrary real normed space in the algebraic and norm/count clauses; reason: the same finite sums and triangle inequalities apply; every norm on real d-dimensional space is an instance, with no completeness hypothesis
--   - encoding: real probability comparisons → extended nonnegative measure values and ENNReal.ofReal on the real comparison bound; reason: probabilities are finite under the product probability law; a negative lower bound becomes the equivalent tautological lower bound zero
--   - encoding: ordinary and conditional expectations of exponentials → Bochner integrals and almost-everywhere conditional expectations, with integrability asserted in Lemma 2.3; reason: fixed-input execution has finitely many measurable sign outcomes, so these exponentials are integrable; no integrability premise or finite input alphabet is added
-- source:
--   Russo–Wei, The Online Steinitz Problem, STOC 2027 submission #22 (2026 preprint), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/22.pdf, SHA-256 32ff14f15a94c95630765c77f4fa5a429fb294bcf03a9055ed67c60658769366, Theorem 2.1, pp.6–7, equations (2.3)–(2.4); Algorithm 1, p.5; proof pp.7–12

import Definitions.Def_OnlineSteinitz_Reduction_Randomness

open MeasureTheory
open scoped BigOperators

namespace OnlineSteinitz.Reduction

/-- Theorem 2.1, pp.6–7, complete: immediate valid placement, causality,
pathwise, deterministic adaptive and fixed-input probabilistic (i), all of
(ii), and the zero-total specialization. No local performance is built into
the router. Arbitrary real normed spaces in (i) include every norm on ℝ^d. -/
theorem signing_to_ordering_reduction : ∃ C : ℝ, 0 < C ∧
    (∀ T : ℕ, 0 < T →
      ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
        (Ω : Type) [MeasurableSpace Ω] (rules : Node T → Signer E Ω)
        (ω : Node T → Ω),
      -- Immediate placements for every legal partial stream, without unit-ball assumptions.
      (∀ xs : List E, xs.length ≤ T →
        let r := execute rules ω xs
        r.placed.map Prod.snd = xs ∧
        (r.placed.map Prod.fst).Nodup ∧
        (∀ p ∈ r.placed, p.1 < T)) ∧
      -- Irrevocability and equality of assignments on identical input histories.
      (∀ (xs ys : List E) (n : ℕ), n ≤ xs.length →
        (execute rules ω xs).placed.take n = (execute rules ω (xs.take n)).placed ∧
        (xs.take n = ys.take n →
          (execute rules ω (xs.take n)).placed = (execute rules ω (ys.take n)).placed)) ∧
      -- Completed permutation, correct capacities, and actual split totals.
      (∀ v : Fin T → E,
        let r := execute rules ω (List.ofFn v)
        (∃ π : Equiv.Perm (Fin T), ∀ j : Fin T,
          output r j.val = v (π j) ∧
          (r.placed[(π j).val]?).map Prod.fst = some j.val) ∧
        (∀ u ∈ internalNodes T,
          (r.localHistory u).length = u.2.val ∧
          leftCount (r.localHistory u) = leftSize u.2.val ∧
          splitError (output r) u = localError u.2.val (r.localHistory u))) ∧
      -- Part (i), exact pathwise estimate (2.3).
      (∀ (v : Fin T → E), (∀ i, ‖v i‖ ≤ 1) → ∀ V W : ℕ → ℝ,
        (∀ u ∈ internalNodes T,
          terminalGood V W u.2.val
            (proposedHistory ((execute rules ω (List.ofFn v)).localHistory u))) →
        prefixGood V W (execute rules ω (List.ofFn v))) ∧
      -- Deterministic guarantees apply to adaptive streams, not just oblivious ones.
      (∀ V W : ℕ → ℝ,
        (∀ u ∈ internalNodes T, ∀ x : Fin u.2.val → E,
          (∀ i, ‖x i‖ ≤ 1) →
          terminalGood V W u.2.val (signHistory (rules u) (ω u) (List.ofFn x))) →
        ∀ adversary : ℕ → List (ℕ × E) → E,
          (∀ t h, t < T → ‖adversary t h‖ ≤ 1) →
          prefixGood V W (adaptiveExecute rules ω adversary)) ∧
      -- Fixed-stream joint local success gives one event for all output prefixes.
      (∀ (μ : Node T → Measure Ω) [∀ u, IsProbabilityMeasure (μ u)],
        (∀ u ∈ internalNodes T, MeasurableSigner (rules u)) → ∀ V W p : ℕ → ℝ,
        (∀ u ∈ internalNodes T, ∀ x : Fin u.2.val → E,
          (∀ i, ‖x i‖ ≤ 1) →
          ENNReal.ofReal (1 - p u.2.val) ≤
            (μ u) {η | terminalGood V W u.2.val (signHistory (rules u) η (List.ofFn x))}) →
        ∀ v : Fin T → E, (∀ i, ‖v i‖ ≤ 1) →
          ENNReal.ofReal (1 - ∑ u ∈ internalNodes T, p u.2.val) ≤
            (tapeLaw μ) {η | prefixGood V W (execute rules η (List.ofFn v))}) ∧
      -- Zero total is a specialization, never a routing input or a premise above.
      (∀ v : Fin T → E, (∑ i, v i) = 0 → ∀ k : ℕ, k ≤ T →
        residual T (output (execute rules ω (List.ofFn v))) k =
          ∑ j ∈ Finset.range k, output (execute rules ω (List.ofFn v)) j)) ∧
    -- Part (ii), (2.4), one absolute constant and every failure parameter.
    (∀ (T d : ℕ), 0 < T → 0 < d →
      ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Node T → Measure Ω)
        [∀ u, IsProbabilityMeasure (μ u)]
        (r : Node T → Signer (Vec (d + 1)) Ω),
      (∀ u ∈ internalNodes T, MeasurableSigner (r u)) → ∀ sigma : ℝ, 1 ≤ sigma →
      (∀ u ∈ internalNodes T, HasScale (μ u) u.2.val (r u) sigma) →
      ∀ v : Fin T → Vec d, (∀ i, ‖v i‖ ≤ 1) → ∀ δ : ℝ, 0 < δ → δ < 1 →
        ENNReal.ofReal (1 - δ) ≤
          (tapeLaw μ) {ω | maxResidual (euclideanRun r v ω) ≤
            C * sigma * (Real.log T + Real.sqrt (Real.log T * (d + Real.log (1 / δ))))}) := by sorry

end OnlineSteinitz.Reduction
