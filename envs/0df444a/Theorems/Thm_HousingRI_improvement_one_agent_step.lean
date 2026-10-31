-- Prove2me | Theorems.Thm_HousingRI_improvement_one_agent_step
-- name    : HousingRI.improvement_one_agent_step
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:20.45698+00:00
-- url     : https://prove2.me/theorems/5fd84b4b-d0f6-42cb-8b19-231156cb9738
-- title:
--   Proof of Theorem 1, p.13 — an improvement splits into one changed agent and the rest (corrected improvement)
-- statement:
--   Let $A$ and $\tilde A$ be preference profiles over the agents and objects $N$ ($j\,R_k\,l$ iff $A_{kl}\le A_{kj}$), let $\tilde R$ be an improvement for agent $i$ with respect to $R$, and let $j\ne i$. Let $R'$ be the profile in which agent $j$ has her preferences from $\tilde R$ and every other agent her preferences from $R$. Then
--
--   1. $R'$ is an improvement for $i$ with respect to $R$,
--   2. $\tilde R$ is an improvement for $i$ with respect to $R'$, and
--   3. if $R$ and $\tilde R$ are strict, so is $R'$.
--
--   Applied once per changed agent, this decomposes any improvement into a chain of improvements in each of which a single agent other than $i$ changes her preferences; the proof of Theorem 1 uses it to reduce to that case.
--
--   **Formalization Note** $R'$ is `Function.update A j (Ã j)`; improvement is the corrected definition (conditions (1)–(4)).
--
--   Differences from the source:
--   - correction: R̃ is an improvement for i: conditions (1)–(3), p.13 → `IsImprovement i A Ã`: (1)–(3) plus (4) for all j ≠ i and k ≠ i, k R̃ⱼ j ⟹ k Rⱼ j; reason: with (1)–(3) alone Theorem 1 is false: N = {1,2,3}, i = 1, R₁: 2 P 1 P 3, R₂: 1 P 2 P 3, R₃: 2 P 3 P 1, and R̃ = R except R̃₂: 3 P 1 P 2 satisfy (1)–(3) (object 3 is unacceptable to agent 2 at R₂); τ(R) = {(1,2),(3)}, τ(R̃) = {(1),(2,3)}, so τ₁(R) = 2 P₁ 1 = τ₁(R̃) and Theorem 1 fails
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - reading: "we repeatedly apply the one-agent result" → the one-step decomposition R → R' → R̃ into two improvements with strictness preserved; reason: this is the property of improvements that repeated application of the one-agent case needs
--   - generalization: finite N = {1, …, n}, n ≥ 2 → any type `N` (no finiteness); reason: the conditions are agent-wise; specializes to the source's N
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, proof of Theorem 1, p.13: "We can assume that there is a unique agent j ≠ i with R̃ⱼ ≠ Rⱼ and prove that x̃ᵢRᵢxᵢ. (If there is more than one such agent, we repeatedly apply the one-agent result to obtain the result.)"

import Mathlib
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_IsImprovement

namespace HousingRI

/-- **Reduction to one changed agent** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, proof
of Theorem 1, p.13): "We can assume that there is a unique agent j ≠ i with R̃ⱼ ≠ Rⱼ and prove
that x̃ᵢRᵢxᵢ. (If there is more than one such agent, we repeatedly apply the one-agent result to
obtain the result.)"

If `R̃` is an improvement for `i` with respect to `R` and `j ≠ i`, let `R'` be `R` with agent
`j`'s preferences replaced by `R̃ⱼ`. Then `R'` is an improvement for `i` with respect to `R`
(only agent `j` changed), `R̃` is an improvement for `i` with respect to `R'` (agent `j` no longer
changes), and `R'` is strict when `R` and `R̃` are. Iterating over the changed agents gives the
chain of one-agent improvements along which the one-agent result is applied.

**Formalization Note.** Preferences are utility matrices; `R'` is `Function.update A j (Ã j)`.
`IsImprovement` is the corrected definition (conditions (1)–(4)). -/
theorem improvement_one_agent_step {N : Type*} [DecidableEq N] (i j : N) (A Ã : N → N → ℝ)
    (himp : IsImprovement i A Ã) (hji : j ≠ i) :
    IsImprovement i A (Function.update A j (Ã j)) ∧
      IsImprovement i (Function.update A j (Ã j)) Ã ∧
      (IsStrict A → IsStrict Ã → IsStrict (Function.update A j (Ã j))) := by sorry

end HousingRI
