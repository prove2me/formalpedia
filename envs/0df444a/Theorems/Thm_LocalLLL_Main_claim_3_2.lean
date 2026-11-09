-- Prove2me | Theorems.Thm_LocalLLL_Main_claim_3_2
-- name    : LocalLLL.Main.claim_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:54:57.206284+00:00
-- url     : https://prove2.me/theorems/46b45789-268d-4d79-ab9c-df4c5d40eadd
-- title:
--   Claim 3.2 — dangerous events, locality and independence (Eq. (1))
-- statement:
--   Let $d\ge3$, $\lambda\ge1000$, and consider a finite variable LLL with each event probability at most $d^{-\lambda}$. Put $k=\lfloor\lambda/16\rfloor$, $q=d^{-\lambda/32}$ and $\rho=d^{-19\lambda/32}$. For every vertex $v$, $D_v$ is measurable, depends only on $X_{V_v}$, and satisfies Eq. (1), with the standing value $p=d^{-\lambda}$:
--
--   $$\Pr[D_v]\le d^{6k}d^{-\lambda}/q\le\rho.$$
--
--   For every fixed $T\subseteq B_G(v,5)$ of size at most $k$, both the retracted marginal $\Pr_{\mathrm{ret}(X,B_G(T,4))}[A_v]$ and its strict exceedance of $q$ depend only on $X_{V_v}$. For every 2-independent set $S$, the events $D_v$, $v\in S$, are mutually independent and
--
--   $$\Pr\Big[\bigcap_{v\in S}D_v\Big]=\prod_{v\in S}\Pr[D_v]\le\rho^{|S|}.$$
--
--   This controls the frequency of dangerous vertices and the joint probabilities needed for amplification.
--
--   Differences from the source:
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: real λ, natural k=⌊λ/16⌋, and retracted marginals → natural floor, real powers, and splice sections integrated against the original product law; reason: λ≥1000 and d≥3 exclude degenerate floors and powers; no conditioning on a null event is introduced
--   - generalization: the observations occur inside Lemma 3.1 with d ≥ d_min and 1000 ≤ λ ≤ a log n → d ≥ 3 and λ ≥ 1000, without λ ≤ a log n or the larger d_min cutoff; reason: these local geometric and probability estimates use only d ≥ 3 and λ ≥ 1000; they contain no round bound or invocation of the exponential solver and specialize to every instance of Lemma 3.1
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), Claim 3.2 and Eq. (1), p. 4 (PDF 5); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- Claim 3.2 with Eq. (1), printed pp. 4–5. All locality and independence clauses. -/
theorem claim_3_2 {ι V : Type} [Fintype V] {α : ι → Type}
    [∀ z, MeasurableSpace (α z)] (μ : ∀ z, Measure (α z))
    [∀ z, IsProbabilityMeasure (μ z)] (G : SimpleGraph V)
    (vars : V → Set ι) (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ)
    (hd : 3 ≤ d) (hlam : 1000 ≤ lam)
    (hinst : variableInstance μ G vars events d ((d : ℝ) ^ (-lam))) :
    (∀ v, MeasurableSet (dangerous μ G vars events d lam v) ∧
      DependsOn (fun x => x ∈ dangerous μ G vars events d lam v) (vars v) ∧
      probability μ (dangerous μ G vars events d lam v) ≤
        (d : ℝ) ^ (6 * packingSize lam) * (d : ℝ) ^ (-lam) / dangerThreshold d lam ∧
      (d : ℝ) ^ (6 * packingSize lam) * (d : ℝ) ^ (-lam) / dangerThreshold d lam ≤
        dangerBound d lam) ∧
    (∀ v (T : Finset V), (↑T : Set V) ⊆ ball G v 5 → T.card ≤ packingSize lam →
      DependsOn (fun x => retractedMarginal μ vars x (balls G (↑T) 4) (events v)) (vars v) ∧
      DependsOn (fun x => dangerThreshold d lam <
        retractedMarginal μ vars x (balls G (↑T) 4) (events v)) (vars v)) ∧
    (∀ S : Finset V, separated G 2 (↑S) →
      iIndepSet (fun s : (↑S : Set V) => dangerous μ G vars events d lam s.1)
        (Measure.infinitePi μ) ∧
      probability μ {x | ∀ v ∈ S, x ∈ dangerous μ G vars events d lam v} =
        ∏ v ∈ S, probability μ (dangerous μ G vars events d lam v) ∧
      probability μ {x | ∀ v ∈ S, x ∈ dangerous μ G vars events d lam v} ≤
        dangerBound d lam ^ S.card) := by sorry

end LocalLLL.Main
