-- Prove2me | Theorems.Thm_LocalLLL_Main_part2_parameters
-- name    : LocalLLL.Main.part2_parameters
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:58.978979+00:00
-- url     : https://prove2.me/theorems/d1c46062-04a0-4a86-8bf0-450b5316f701
-- title:
--   §3.2 Part II — amplified parameters (Eq. (2))
-- statement:
--   Let $d\ge3$, $\lambda\ge1000$, and let $\Pi$ be a finite variable LLL of degree at most $d$ and event probabilities at most $d^{-\lambda}$. Put $k=\lfloor\lambda/16\rfloor$ and $\rho=d^{-19\lambda/32}$. The constructed event $F_v$ is measurable and determined by $\bigcup_{u\in B_G(v,11)}V_u$. The graph $G^{23}$ contains all shared-variable dependency edges and has degree at most $d^{23}$. Every link of Eq. (2) holds:
--
--   $$\Pr[F_v]\le\sum_{\substack{S\subseteq B_G(v,11),\ |S|=k+1\\ S\text{ 2-independent}}}\Pr\Big[\bigcap_{u\in S}D_u\Big]\le d^{11(k+1)}\rho^{k+1}=d^{-(19\lambda/32-11)(k+1)}\le(d^{23})^{-\lambda^2/700}.$$
--
--   Thus the new LLL is on the same independent variables, with one event per original vertex and exponent $\lambda^2/700$.
--
--   Differences from the source:
--   - reading: independent random variables without stated domain restrictions → arbitrary measurable variable spaces, arbitrary index set and unrestricted coordinate sets; reason: Reading V: no countability, standard-Borel or finite-domain restriction is imposed
--   - encoding: variable universes without a universe-level convention → ι and α take values in Lean Type; reason: fixes universe levels without a finite, countable or measurable-space regularity restriction
--   - encoding: independent variables and their event probabilities → infinitePi product law and real probabilities, with a probability measure on every coordinate; reason: measurable bad events and coordinate laws represent the stated independent random variables; the product is a probability law, so toReal has no infinite-value default
--   - encoding: finite graph distances, balls, powers and cardinalities → finite vertex types, extended distance and natural neighbor-set cardinalities; reason: disconnected pairs have infinite distance and graph powers remain loopless; cardinalities agree on finite graphs
--   - encoding: real λ, natural k=⌊λ/16⌋, and retracted marginals → natural floor, real powers, and splice sections integrated against the original product law; reason: λ≥1000 and d≥3 exclude degenerate floors and powers; no conditioning on a null event is introduced
--   - generalization: the observations occur inside Lemma 3.1 with d ≥ d_min and 1000 ≤ λ ≤ a log n → d ≥ 3 and λ ≥ 1000, without λ ≤ a log n or the larger d_min cutoff; reason: these local geometric and probability estimates use only d ≥ 3 and λ ≥ 1000; they contain no round bound or invocation of the exponential solver and specialize to every instance of Lemma 3.1
-- source:
--   Maxime Flin, Mohsen Ghaffari, Magnus M. Halldorsson, Yannic Maus, Alexandre Nolin, STOC 2027 submission #475 (October 2026), §3.2 Part II and Eq. (2), p. 5 (PDF 6); source.pdf, SHA-256 3dde5fa7cf9bc55426bf80a9dd9632c790e2ea3d0fe4a19b924d1802d48000a2.

import Mathlib
import Definitions.Def_LocalLLL_Main_Repair

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable Classical.decEq

namespace LocalLLL.Main

/-- §3.2 Part II and every link of Eq. (2), printed p. 5. -/
theorem part2_parameters {ι V : Type} [Fintype V] {α : ι → Type}
    [∀ z, MeasurableSpace (α z)] (μ : ∀ z, Measure (α z))
    [∀ z, IsProbabilityMeasure (μ z)] (G : SimpleGraph V)
    (vars : V → Set ι) (events : V → Set (Assignment α)) (d : ℕ) (lam : ℝ)
    (hd : 3 ≤ d) (hlam : 1000 ≤ lam)
    (hinst : variableInstance μ G vars events d ((d : ℝ) ^ (-lam))) :
    variableInstance μ (graphPower G 23) (amplifiedVars G vars)
      (amplifiedEvent μ G vars events d lam) (d ^ 23)
      (((d : ℝ) ^ (23 : ℕ)) ^ (-(lam ^ 2 / 700))) ∧
    (∀ v,
      probability μ (amplifiedEvent μ G vars events d lam v) ≤
        ∑ S ∈ (Finset.univ : Finset V).powerset.filter (fun (S : Finset V) =>
          (↑S : Set V) ⊆ ball G v 11 ∧ S.card = packingSize lam + 1 ∧ separated G 2 (↑S)),
          probability μ {x | ∀ u ∈ S, x ∈ dangerous μ G vars events d lam u}) ∧
    (∀ v,
      (∑ S ∈ (Finset.univ : Finset V).powerset.filter (fun (S : Finset V) =>
          (↑S : Set V) ⊆ ball G v 11 ∧ S.card = packingSize lam + 1 ∧ separated G 2 (↑S)),
          probability μ {x | ∀ u ∈ S, x ∈ dangerous μ G vars events d lam u}) ≤
        (d : ℝ) ^ (11 * (packingSize lam + 1)) * dangerBound d lam ^ (packingSize lam + 1)) ∧
    (d : ℝ) ^ (11 * (packingSize lam + 1)) * dangerBound d lam ^ (packingSize lam + 1) =
      (d : ℝ) ^ (-(19 * lam / 32 - 11) * ((packingSize lam : ℝ) + 1)) ∧
    (d : ℝ) ^ (-(19 * lam / 32 - 11) * ((packingSize lam : ℝ) + 1)) ≤
      ((d : ℝ) ^ (23 : ℕ)) ^ (-(lam ^ 2 / 700)) := by sorry

end LocalLLL.Main
