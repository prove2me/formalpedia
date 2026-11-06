-- Prove2me | Theorems.Thm_GradedReserve_lemma_3_3
-- name    : GradedReserve.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:35:05.235657+00:00
-- url     : https://prove2.me/theorems/fb970dd5-4fc2-4db5-9bab-954cf18b50be
-- title:
--   Lemma 3.3 — symmetric equilibria of $G_\pi$ share utilities, allocations and trading bids
-- statement:
--   Let $n\ge2$ bidders have i.i.d. values with a density $f$ on $[0,1]$, positive on $(0,1)$, and let $F$ be regular (the standing assumptions of Section 3).
--   For every graded reserve $\pi$, any two symmetric Bayes–Nash equilibria $\sigma_1,\sigma_2$ of $G_\pi$ (mixed strategies allowed)
--
--   1. have the same utilities: $U_1(v)=U_2(v)$ for every $v\in[0,1]$;
--   2. have the same interim allocations almost everywhere: $q_1=q_2$ a.e.;
--   3. have the same bids almost everywhere on the set of types that trade with positive probability: for almost every $v$ with $q_1(v)>0$, both equilibria prescribe the same single bid to type $v$.
--
--   The lemma is what makes the guarantee of Definition 2.1 checkable from one equilibrium: all symmetric equilibria of a graded reserve have the same revenue.
--
--   **Formalization Note** Utilities are the interim utilities $\sup_a u(v,a)$. "The same bids" is read as: $\sigma_1(v)$ and $\sigma_2(v)$ are the same point mass.
--
--   Differences from the source:
--   - encoding: a distribution F on [0,1] whose density f is positive on (0,1) → IsValueDensity f (f measurable, ≥ 0 on [0,1], > 0 on (0,1), ∫₀¹ f = 1), F(v) = ∫₀^v f; reason: the paper's model; the same distributions
--   - encoding: F regular: φ strictly increasing → StrictMonoOn φ (0,1); reason: φ is defined where f > 0; the same laws
--   - encoding: symmetric BNE β, mixed strategies allowed (p.13), with an exit action → a Markov kernel σ from values to actions in ℝ; negative actions are exit, bids lie in [0,1], no mass above 1; reason: Lean convention (no measurable space on Option ℝ); the same strategies
--   - reading: a Bayes–Nash equilibrium (every type best-responds) → almost every type (for the value law) best-responds; reason: the paper's proofs work up to null sets of types ("apart from a null set", p.14); a single type has probability zero
--   - encoding: sells to the highest bidder with probability π(b₍₁₎); ties broken uniformly at random → W(b) = π(b) Σ_j C(n−1,j) a^j c^{n−1−j}/(j+1) against n − 1 i.i.d. opponents; reason: the same winning probability
--   - encoding: non-decreasing π : [0,1] → [0,1] → π : ℝ → ℝ, monotone with values in [0,1] on [0,1]; reason: only values on [0,1] are used; the same mechanisms
--   - encoding: U(v), the equilibrium utility of type v → interimUtility = sup over actions of the payoff, for every v; reason: equal to the equilibrium utility for almost every type; defined at every type
--   - reading: the same bids almost everywhere on the set of types that trade with positive probability → for a.e. v with q₁(v) > 0, σ₁(v) = σ₂(v) = δ_b for one bid b; reason: the proof shows the trading part of every symmetric BNE is pure a.e. (p.14), so "the bid" of a trading type is a point mass
-- source:
--   Chen–Wang, Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee, manuscript (STOC 2027 submission; PDF sha256 6b1da440…1bab), Lemma 3.3, p.7 (PDF 8); proof pp.13–14 (PDF 14–15)

import Mathlib
import Definitions.Def_GradedReserve_IsGradedReserve
import Definitions.Def_GradedReserve_IsRegular
import Definitions.Def_GradedReserve_IsSymBNE
import Definitions.Def_GradedReserve_IsValueDensity
import Definitions.Def_GradedReserve_interimAlloc
import Definitions.Def_GradedReserve_interimUtility
import Definitions.Def_GradedReserve_typeMeasure
open MeasureTheory ProbabilityTheory Set Filter Topology

namespace GradedReserve

/-- **Lemma 3.3** (Symmetric equilibria) (Chen–Wang, *Optimal Auctions for Anchored Bidders under a Rational Revenue Guarantee*, manuscript (STOC 2027 submission), Lemma 3.3, p.7, PDF 8; proof pp.13–14, PDF 14–15):
for every `G_π ∈ G`, any two symmetric BNE have the same utilities, the same interim allocations
almost everywhere, and the same bids almost everywhere on the set of types that trade with
positive probability.

**Formalization Note.** Section 3's standing assumptions (value density on `[0, 1]`, positive on
`(0, 1)`; `F` regular; `n ≥ 2`) are hypotheses. Equilibria may be mixed. Utilities are the interim
utilities `sup_a payoff(v, a)`, equal at every `v ∈ [0, 1]`. "The same bids" is read as: for almost
every type with positive interim allocation, both strategies are the same point mass. -/
theorem lemma_3_3 (f : ℝ → ℝ) (n : ℕ) (hn : 2 ≤ n) (hf : IsValueDensity f) (hreg : IsRegular f)
    (π : ℝ → ℝ) (hπ : IsGradedReserve π) (σ₁ σ₂ : Kernel ℝ ℝ)
    (h₁ : IsSymBNE f n π σ₁) (h₂ : IsSymBNE f n π σ₂) :
    (∀ v ∈ Icc (0:ℝ) 1, interimUtility f n π σ₁ v = interimUtility f n π σ₂ v) ∧
    (interimAlloc f n π σ₁ =ᵐ[typeMeasure f] interimAlloc f n π σ₂) ∧
    (∀ᵐ v ∂(typeMeasure f), 0 < interimAlloc f n π σ₁ v →
      ∃ b, σ₁ v = Measure.dirac b ∧ σ₂ v = Measure.dirac b) := by sorry

end GradedReserve
