-- Prove2me | Theorems.Thm_LearnManip_lemma_1
-- name    : LearnManip.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T18:59:06.492453+00:00
-- url     : https://prove2.me/theorems/ccf38426-244f-41f5-852a-3b4d5dd14530
-- title:
--   Lemma 1, p.12 (corrected: uniqueness in a growth class) — uniqueness clause; existence, value and policy are clauses (B), (A), (E) of the goal
-- statement:
--   Let $w_1,w_2$ be measurable functions of $(\mu,s,c)$ with $|w_i(\mu,s,c)-\mu/(1-\alpha)|\le A(1+s)$ for some $A$. If both solve the BDP equation (10), then
--   $$w_1=w_2.$$
--
--   This is the uniqueness half of Lemma 1. It is what lets a closed-form solution be identified as the solution.
--
--   Lemma 1's existence of a solution, its identification with the value function (8), and the optimality of a maximizer are clauses (B), (A) and (E) of the goal theorem.
--
--   Differences from the source:
--   - correction: there exists a unique solution (proved on the bounded Borel functions) → uniqueness among measurable w with |w − µ/(1−α)| ≤ A(1+s); reason: no bounded solution exists, since q = 0, Λ = 1 gives Tv ≥ µ + αv(µ, s, cη), and at α = 1/2, η = 2 the function v + c is a second solution; the variance never increases, so the weight 1 + s gives a contraction
--   - encoding: a distortion rule Λ ∈ D_{µ^q} → the distorted law G ≪ N(µ, σ²_{µ^q}) with y G-integrable, and the cost γ KL(G‖N); reason: (4) is a bijection Λ ↔ P^Λ with Λ = dP^Λ/dP, and E[Λ log Λ] is the relative entropy
--   - encoding: supremum over all Λ in (10) → pairs (q, G) of finite relative entropy, with IsLUB; reason: a distortion of infinite relative entropy has objective −∞, so excluding it changes no supremum
-- source:
--   Keppo, Kim, Zhang, Learning Manipulation Through Information Dissemination (SSRN 3465030, 2021-09-04), Lemma 1, p.12; proof, pp.ec6–ec7 (PDF 45–46)

import Mathlib
import Definitions.Def_LearnManip_Params
import Definitions.Def_LearnManip_IsBDPSolution
import Definitions.Def_LearnManip_InClass

open scoped NNReal ENNReal Topology
open MeasureTheory ProbabilityTheory InformationTheory Filter

namespace LearnManip

/-- Lemma 1, p.12, of Keppo, Kim, Zhang (SSRN 3465030, 2021-09-04), its uniqueness clause,
**corrected**: two solutions of the BDP equation (10) in the growth class `InClass` coincide.

**Formalization Note.** As printed the lemma is false (no bounded solution; at `α = 1/2`, `η = 2`,
`v + c` is a second solution). The lemma's other clauses (existence, identification with `V`,
optimality of a maximizer) are clauses (B), (A), (E) of `theorem_2`. -/
theorem lemma_1 (P : Params) {w₁ w₂ : ℝ → ℝ≥0 → ℝ≥0 → ℝ} (h₁ : InClass P w₁) (h₂ : InClass P w₂)
    (s₁ : IsBDPSolution P w₁) (s₂ : IsBDPSolution P w₂) (μ : ℝ) (s c : ℝ≥0) :
    w₁ μ s c = w₂ μ s c := by sorry

end LearnManip
