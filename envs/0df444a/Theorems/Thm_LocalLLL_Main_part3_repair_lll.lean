-- Prove2me | Theorems.Thm_LocalLLL_Main_part3_repair_lll
-- name    : LocalLLL.Main.part3_repair_lll
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:14.886184+00:00
-- url     : https://prove2.me/theorems/15147e82-1d13-4e75-9b56-25a5d6efa557
-- title:
--   §3.2 Part III — repair LLL and exponential criterion (Eq. (3))
-- statement:
--   Let $d\ge3$, $\lambda\ge1000$ and $\Pr[A_v]\le d^{-\lambda}$. Let $x,S$ satisfy the preceding center conditions, and fix injective identifiers. Define $E_s$ by assigning each affected event to its least-identifier eligible center and taking the section over erased coordinates. For any $C>0$ with $d\ge2^{3C}$, these are measurable variable LLL events on the original variable universe, with dependency graph $G^{11}[S]$, degree at most $k=\lfloor\lambda/16\rfloor$, and
--
--   $$\Pr[E_s]\le d^5q=d^{5-\lambda/32}\le d^{-\lambda/40}=2^{-(\lambda/40)\log_2d}\le2^{-Ck}.$$
--
--   Every assignment avoiding all $E_s$, spliced with the retained values of $x$, avoids all original events. This is the exponential-criterion repair problem, including its final correctness implication.
--
--   Differences from the source:
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: real λ, natural k=⌊λ/16⌋, and retracted marginals → natural floor, real powers, and splice sections integrated against the original product law; reason: λ≥1000 and d≥3 exclude degenerate floors and powers; no conditioning on a null event is introduced
--   - generalization: unique identifiers in the usual LOCAL model → arbitrary injective natural identifiers, without a polynomial size bound; reason: random short identifiers can be generated with sufficiently small collision probability; the theorem specializes to bounded identifiers
--   - generalization: the observations occur inside Lemma 3.1 with d ≥ d_min and 1000 ≤ λ ≤ a log n → d ≥ 3 and λ ≥ 1000, with arbitrary C > 0 satisfying d ≥ 2^(3C); reason: the local geometric and probability estimates use only these numerical lower bounds; no λ upper cutoff or round bound is needed, and substituting Lemma 2.2’s C and the source d_min recovers the source claim
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.2 Part III and Eq. (3), p. 6 (PDF 7); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- §3.2 Part III Eq. (3), printed pp. 6–7. Repair events are constructed sections. -/
theorem part3_repair_lll {ι V : Type} [Fintype V] {α : ι → Type}
    [∀ z, MeasurableSpace (α z)] (μ : ∀ z, Measure (α z))
    [∀ z, IsProbabilityMeasure (μ z)] (G : SimpleGraph V)
    (vars : V → Set ι) (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ)
    (hd : 3 ≤ d) (hlam : 1000 ≤ lam)
    (hinst : variableInstance μ G vars events d ((d : ℝ) ^ (-lam)))
    (id : V → ℕ) (hid : Function.Injective id) (x : Assignment α) (S : Set V)
    (hcenters : centerConditions μ G vars events d lam x S)
    (C : ℝ) (hC : 0 < C) (hdC : (2 : ℝ) ^ (3 * C) ≤ (d : ℝ)) :
    variableInstance μ (repairGraph G S) (repairVars G id vars S)
      (repairEvent G id vars events S x) (packingSize lam)
      ((2 : ℝ) ^ (-C * (packingSize lam : ℝ))) ∧
    (∀ s : S,
      probability μ (repairEvent G id vars events S x s) ≤ (d : ℝ) ^ (5 : ℕ) * dangerThreshold d lam) ∧
    (d : ℝ) ^ (5 : ℕ) * dangerThreshold d lam = (d : ℝ) ^ (5 - lam / 32) ∧
    (d : ℝ) ^ (5 - lam / 32) ≤ (d : ℝ) ^ (-lam / 40) ∧
    (d : ℝ) ^ (-lam / 40) = (2 : ℝ) ^ (-(lam / 40) * (Real.log (d : ℝ) / Real.log 2)) ∧
    (2 : ℝ) ^ (-(lam / 40) * (Real.log (d : ℝ) / Real.log 2)) ≤
      (2 : ℝ) ^ (-C * (packingSize lam : ℝ)) ∧
    (∀ z : Assignment α, (∀ s : S, z ∉ repairEvent G id vars events S x s) →
      ∀ v, splice x z (erased G vars S) ∉ events v) := by sorry

end LocalLLL.Main
