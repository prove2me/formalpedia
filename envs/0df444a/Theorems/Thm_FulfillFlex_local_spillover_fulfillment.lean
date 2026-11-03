-- Prove2me | Theorems.Thm_FulfillFlex_local_spillover_fulfillment
-- name    : FulfillFlex.local_spillover_fulfillment
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T04:27:39.444351+00:00
-- url     : https://prove2.me/theorems/f0d299ae-d5e2-4bee-969f-d0870c06f786
-- title:
--   Appendix B.3.1, p.51 — under $\pi$, expected local and spillover fulfillment are at most $f^*$
-- statement:
--   Let $(f^*,l^*)$ be a structured optimal solution of the DLP (5) at $m=T\mu$, $r=T\mathbf b$, and let $\pi$ be the spillover limit policy with limits $\theta=f^*$. Then, over $T$ days from inventory $T\mathbf b$,
--
--   $$
--   \mathbb E[\text{local fulfillment at }j]\le f^*_{jj}\quad\text{for every }j,
--   \qquad
--   \mathbb E[\text{spillover }j'\to j]\le f^*_{j'j}\quad\text{for }j'\ne j.
--   $$
--
--   These are the first two of the three parts in which the proof of Proposition 3 bounds the cost of $\pi$.
--
--   Differences from the source:
--   - reading: "is less than f∗" → ≤ f*; reason: the paper's own argument gives ≤, with equality possible
--   - encoding: μj = E[Dtj] is a real number (p.16) → hypothesis FiniteMean ν (E[D^t_j] < ∞ for every j); reason: the paper presupposes a finite mean when it defines μj; in ℝ≥0∞ an infinite mean would be ⊤, and the hypothesis excludes exactly that undefined case
--   - reading: links A, a set of ordered pairs (p.5) → (j, j) ∈ A for every j; reason: local fulfillment is always available and (5) forces f_jj = 0 off A; Assumption 2 is claimed for Example 1, whose links (1,2), (2,1) force (1,1) ∈ A by transitivity
--   - reading: Proposition 3 and Lemma 8 say "under Assumption 2" → Assumption 1 is also a hypothesis; reason: Assumption 1 is standing from p.6, and the proof uses it (Lemma 8, Case 2; the bound on local fulfillment; linear scaling)
--   - reading: unit demand, inventory r = Tb with b arbitrary → real inventory, one unit per shipment, a DC has inventory when remaining stock ≥ 1; reason: Tb need not be an integer; for integer Tb this is exactly the paper's model
--   - reading: DC j′ "has not fulfilled more than θj′j units" (p.11) → j′ is eligible when spill j′ j + 1 ≤ θ j′ j; reason: the proof says "the policy can not fill more than f∗j′j" (p.51), so at most θ units are filled
--   - reading: "the lowest cost flexible DC" (p.11), ties open → ties go to the smallest index; reason: any fixed rule gives a valid policy, and the proof never uses the order among sources
--   - reading: a unit "not filled locally" abandons independently with probability αj (p.5) → one independent coin per arrival, read exactly when local stock is empty, before a source is sought; reason: the type-one lost sales of the proof (p.51) flip the coin at the stockout; if no source is eligible the order is lost either way
--   - reading: a spillover limit policy may also set an aggregate limit θj (pp.11–12) → no aggregate limit; reason: unspecified limits are non-binding (p.12), and the proof of Proposition 3 sets none
--   - encoding: E[·] of costs and counts → sums in ℝ≥0∞, compared through ENNReal.ofReal; reason: a Bochner integral of a non-integrable function would be 0; path costs are nonnegative under Assumption 1
--   - encoding: daily demand as random variables D^t_j on an unnamed probability space → a PMF ν on DC N → ℕ, with arrivals and coins a PMF on lists; reason: every law on this countable type is a PMF, and no independence across DCs is imposed
-- source:
--   DeValve, Wei, Wu, Yuan, Understanding the Value of Fulfillment Flexibility in an Online Retailing Environment, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, "Local Fulfillment" and "Spillover Fulfillment", p.51

import Mathlib
import Definitions.Def_FulfillFlex_Assumption1
import Definitions.Def_FulfillFlex_IsDLPOptimal
import Definitions.Def_FulfillFlex_meanDemand
import Definitions.Def_FulfillFlex_expectedCost

namespace FulfillFlex

/-- **Local and spillover fulfillment under `π`.**
DeValve, Wei, Wu, Yuan, SSRN 3265838 (2021-01-18 version), Appendix B.3.1, "Local Fulfillment" and
"Spillover Fulfillment", p.51. Let `π` be the spillover limit policy with limits `θ = f*`, for an
optimal solution `(f*, l*)` of (5) with the properties of Lemma 8 and of its consequence, at
`r = T • b`. The expected amount of local fulfillment at DC `j` is at most `f*_jj`, and for
`j' ≠ j` the expected amount of DC `j` demand filled from DC `j'` is at most `f*_{j'j}`.

**Formalization Note** Daily demand only needs a finite mean here (the paper's `μ_j`); finite
variance is used only by the lost-sales bound. -/
theorem local_spillover_fulfillment {N : ℕ} (A : Set (DC N × DC N)) (c : DC N → DC N → ℝ)
    (p : DC N → ℝ) (α : DC N → unitInterval) (b : DC N → ℝ) (ν : PMF (DC N → ℕ))
    (hdiag : ∀ j, (j, j) ∈ A) (hA1 : Assumption1 A c p) (hb : ∀ j, 0 ≤ b j)
    (hν : FiniteMean ν) (T : ℕ) (hT : 1 ≤ T) (f : DC N → DC N → ℝ) (l : DC N → ℝ)
    (hf : IsStructuredOptimal A c p α ((T : ℝ) • meanDemand ν) ((T : ℝ) • b) f l) :
    (∀ j, expectedLocal ν α A c f ((T : ℝ) • b) T j ≤ ENNReal.ofReal (f j j)) ∧
      ∀ j' j, j' ≠ j → expectedSpill ν α A c f ((T : ℝ) • b) T j' j ≤ ENNReal.ofReal (f j' j) := by sorry

end FulfillFlex
