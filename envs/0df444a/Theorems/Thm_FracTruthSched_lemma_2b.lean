-- Prove2me | Theorems.Thm_FracTruthSched_lemma_2b
-- name    : FracTruthSched.lemma_2b
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T01:33:43.363441+00:00
-- url     : https://prove2.me/theorems/62ea3e25-3d6c-4504-95f8-e4fe7b9f0ac0
-- title:
--   Lemma 2 (b) — two-task separation for almost every opposing value
-- statement:
--   Let $\ell\ge2$ and let $(x,P)$ be a feasible truthful mechanism on the graph inputs of $MC_\ell$ with eligibility (i) and zero-type irrelevance (iii). Choose two tasks $e,f$ with the same endpoints $i,j$, and fix all values on the other tasks (a base graph input $z$). Write $t=(t_1,t_2)$ for machine $i$'s values on $e$ and $f$, $s=(s_1,s_2)$ for machine $j$'s values on them, and $V_i(t;s)$ for machine $i$'s disutility in the $(e,f)$-slice. Then for almost every $s\in(0,\infty)^2$,
--   $$V_i(t_1,t_2;s)=V_i(t_1,0;s)+V_i(0,t_2;s)\qquad\text{for every } t\in\mathbb R^2_{\ge0}.\tag{8}$$
--   One exceptional null set of opposing values serves every own value $t$. The statement holds for either endpoint in the role of $i$, which covers the corresponding statement for $V_j$.
--
--   Two-task separation turns zero-type irrelevance into additivity of a machine's disutility over parallel tasks, the key to the fixed-star bound.
--
--   Differences from the source:
--   - generalization: a limit mechanism on MC_ℓ (Definition 6: the mechanism constructed in Lemma 1) → every feasible truthful mechanism on the graph inputs of MC_ℓ with eligibility (i) and zero-type irrelevance (iii); reason: p.11: 'The proof uses only truthfulness, eligibility, and zero-type irrelevance. Consequently, the lemma also holds for any mechanism satisfying properties (i)–(iv) of Lemma 1'; every limit mechanism has these properties by Lemma 1, so the statement specializes to the source's
--   - reading: for almost every s ∈ (0,∞)², (8) for every t ∈ ℝ²_{≥0} → ∀ᵐ s for Lebesgue measure restricted to (0,∞)², ∀ t₁ t₂ ≥ 0; reason: App. B, p.28: one exceptional set for all own values ('The order of quantifiers is essential'); the stronger of the two quantifier orders
--   - encoding: the corresponding statements for V_j, with the roles of the two machines exchanged → the endpoint pair (i, j) is either ordering of the class's two machines; reason: same statements
--   - encoding: the disutility in the (e, f)-slice (§2.3) → pairSliceDisutility: full disutility at the slice input minus its value at own values (0,0) on (e, f); reason: the restriction formula (6) of §2.3
--   - encoding: a graph input of MC_ℓ: the two endpoint values of every edge and the owner value of every self-loop, all nonnegative, and no other values → t : Fin n → CoreTask n ℓ → ℝ, nonnegative and 0 at every (machine, task) pair that is not incident (IsGraphInput); edges of Q{u,v} are encoded with u < v; reason: a machine's cost Σ_e t_ie x_ie is then its cost on its incident tasks; same inputs and same costs
-- source:
--   Anastasiadis et al., Tight bounds for fractional and randomized truthful scheduling, arXiv:2611.06642v1, Lemma 2 (b), p.11; proof in App. B, pp.27–28

import Mathlib
import Definitions.Def_FracTruthSched_IsFeasibleOn
import Definitions.Def_FracTruthSched_IsTruthfulOn
import Definitions.Def_FracTruthSched_IsGraphInput
import Definitions.Def_FracTruthSched_IsEligible
import Definitions.Def_FracTruthSched_HasZeroTypeIrrelevance
import Definitions.Def_FracTruthSched_pairSliceDisutility

set_option autoImplicit false

namespace FracTruthSched

open MeasureTheory

/-- **Lemma 2 (b) (Two-task separation, almost every opposing value)** (Anastasiadis et al.,
arXiv:2611.06642v1, Lemma 2 (b), p.11; proof in App. B, pp.27–28). Choose two tasks `e, f` with the
same endpoints `i, j`, and fix all values on the other tasks. With `t = (t₁, t₂)` machine `i`'s values
and `s = (s₁, s₂)` machine `j`'s values on `e, f`, and `V_i(t; s)` machine `i`'s disutility in the
`(e, f)`-slice, the identity (8) `V_i(t₁, t₂; s) = V_i(t₁, 0; s) + V_i(0, t₂; s)` holds for every
`t ∈ ℝ²_{≥0}`, for almost every `s ∈ (0, ∞)²`.

**Formalization Note.** Stated for every feasible truthful mechanism on `MC_ℓ` with eligibility (i)
and zero-type irrelevance (iii) (p.11: "The proof uses only truthfulness, eligibility, and zero-type
irrelevance"), every pair of distinct parallel edges `e = (p, k₁)`, `f = (p, k₂)`, every base graph
input `z` and **both** orderings of the endpoints (the case `i = p.2, j = p.1` is "the corresponding
statement for V_j"). `s : ℝ × ℝ`; "almost every" is for Lebesgue measure on `(0, ∞)²`, with one null
set serving every own value `t` (`∀ᵐ s, ∀ t`, App. B, p.28: "The order of quantifiers is
essential"). -/
theorem lemma_2b {n ℓ : ℕ} (hℓ : 2 ≤ ℓ) (M : FracMech n (CoreTask n ℓ))
    (hfeas : IsFeasibleOn IsGraphInput M) (htruth : IsTruthfulOn IsGraphInput M)
    (hel : IsEligible M) (hzti : HasZeroTypeIrrelevance M)
    (p : {p : Fin n × Fin n // p.1 < p.2}) (k₁ k₂ : Fin ℓ) (hk : k₁ ≠ k₂) (i j : Fin n)
    (hij : (i = p.1.1 ∧ j = p.1.2) ∨ (i = p.1.2 ∧ j = p.1.1))
    (z : Fin n → CoreTask n ℓ → ℝ) (hz : IsGraphInput z) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ))), ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → 0 ≤ t₂ →
      pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (t₁, t₂) s =
        pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (t₁, 0) s +
          pairSliceDisutility M z i j (.inl (p, k₁)) (.inl (p, k₂)) (0, t₂) s := by sorry

end FracTruthSched
