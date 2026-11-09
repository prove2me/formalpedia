-- Prove2me | Theorems.Thm_LocalLLL_Main_part3_retraction_bound
-- name    : LocalLLL.Main.part3_retraction_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:38.959235+00:00
-- url     : https://prove2.me/theorems/c47ca8ee-0bd6-466b-a72a-0109635b6bbe
-- title:
--   §3.2 Part III — marginals after retraction near centers
-- statement:
--   In the same setting, let $x$ avoid all amplified events. Let $D$ be its dangerous vertices, and suppose $S\subseteq D$ is 2-independent and $D\subseteq B_G(S,4)$. Set $W=\bigcup_{u\in B_G(S,4)}V_u$. Then
--
--   $$\forall v,\qquad \Pr_{\mathrm{ret}(x,B_G(S,4))}[A_v]\le q=d^{-\lambda/32}.$$
--
--   If $V_v\cap W=\varnothing$, every completion of the erased coordinates avoids $A_v$. This is permanent nonviolation, not just a probability bound for one resampling. The centers are any sets with these geometric properties.
--
--   Differences from the source:
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: real λ, natural k=⌊λ/16⌋, and retracted marginals → natural floor, real powers, and splice sections integrated against the original product law; reason: λ≥1000 and d≥3 exclude degenerate floors and powers; no conditioning on a null event is introduced
--   - generalization: the observations occur inside Lemma 3.1 with d ≥ d_min and 1000 ≤ λ ≤ a log n → d ≥ 3 and λ ≥ 1000, without λ ≤ a log n or the larger d_min cutoff; reason: these local geometric and probability estimates use only d ≥ 3 and λ ≥ 1000; they contain no round bound or invocation of the exponential solver and specialize to every instance of Lemma 3.1
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.2 Part III retraction bound, p. 6 (PDF 7); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- §3.2 Part III, printed p. 6: small marginals and permanent nonviolation. -/
theorem part3_retraction_bound {ι V : Type} [Fintype V] {α : ι → Type}
    [∀ z, MeasurableSpace (α z)] (μ : ∀ z, Measure (α z))
    [∀ z, IsProbabilityMeasure (μ z)] (G : SimpleGraph V)
    (vars : V → Set ι) (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ)
    (hd : 3 ≤ d) (hlam : 1000 ≤ lam)
    (hinst : variableInstance μ G vars events d ((d : ℝ) ^ (-lam)))
    (x : Assignment α) (S : Set V)
    (hcenters : centerConditions μ G vars events d lam x S) :
    (∀ v, retractedMarginal μ vars x (balls G S 4) (events v) ≤ dangerThreshold d lam) ∧
    (∀ v, Disjoint (vars v) (erased G vars S) →
      ∀ z : Assignment α, splice x z (erased G vars S) ∉ events v) := by sorry

end LocalLLL.Main
