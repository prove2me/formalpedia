-- Prove2me | Theorems.Thm_HousingRI_strongCore_unchanged_of_not_improved
-- name    : HousingRI.strongCore_unchanged_of_not_improved
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:19.912999+00:00
-- url     : https://prove2.me/theorems/6fe32f7d-15f5-4453-8548-e29660e56546
-- title:
--   Proof of Theorem 1, p.13 — if $x_j\,\tilde P_j\,i$ then $\tilde x = x$ (corrected improvement)
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$.
--
--   Let $R$ and $\tilde R$ be strict profiles such that $\tilde R$ is an improvement for $i$ with respect to $R$, and suppose every agent other than one agent $j\ne i$ has the same preferences at $R$ and $\tilde R$. Let $x$ be the strong core allocation at $R$. If agent $j$ strictly prefers her allotment to object $i$ at $\tilde R$,
--
--   $$x_j\,\tilde P_j\,i,$$
--
--   then $x$ is in the strong core at $\tilde R$ and is the only allocation there, i.e. $\tilde x=\tau(\tilde R)=x$.
--
--   This disposes of the case in which the improvement does not reach agent $j$'s allotment, so that the proof of Theorem 1 may assume $i\,\tilde R_j\,x_j$.
--
--   **Formalization Note** Improvement is the corrected definition (conditions (1)–(4)). "$\tilde x=x$" is stated as: $x$ is in the strong core at $\tilde R$, and every strong core allocation at $\tilde R$ equals $x$.
--
--   Differences from the source:
--   - correction: R̃ is an improvement for i: conditions (1)–(3), p.13 → `IsImprovement i A Ã`: (1)–(3) plus (4) for all j ≠ i and k ≠ i, k R̃ⱼ j ⟹ k Rⱼ j; reason: with (1)–(3) alone Theorem 1 is false: N = {1,2,3}, i = 1, R₁: 2 P 1 P 3, R₂: 1 P 2 P 3, R₃: 2 P 3 P 1, and R̃ = R except R̃₂: 3 P 1 P 2 satisfy (1)–(3) (object 3 is unacceptable to agent 2 at R₂); τ(R) = {(1,2),(3)}, τ(R̃) = {(1),(2,3)}, so τ₁(R) = 2 P₁ 1 = τ₁(R̃) and Theorem 1 fails
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type `N`; reason: the statement specializes to `N = Fin n`, n ≥ 2
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - encoding: allocation x ∈ N^N with ∪ᵢ{xᵢ} = N → bijection `x : N → N`; reason: for finite N a surjective self-map is a bijection; same instances
--   - encoding: condition (1) of "S weakly blocks x": {zᵢ : i ∈ S} = S → `∀ i ∈ S, z i ∈ S` with z a bijection; reason: for a bijection of a finite set the two are equivalent
--   - encoding: R̃ₖ = Rₖ → `SamePref A Ã k`: the rows of A and Ã induce the same weak order; reason: preferences are ordinal; equality of the relations is equivalence of the orders
--   - generalization: a unique agent j ≠ i with R̃ⱼ ≠ Rⱼ → every agent k ≠ j has the same preferences (j itself may also be unchanged); reason: covers the source's case and in addition the case with no changed agent
--   - encoding: x = τ(R) and x̃ = τ(R̃) with conclusion x̃ = x → `x` any strong core allocation of A; conclusion: `x` is in the strong core of Ã and every strong core allocation of Ã equals `x`; reason: τ is the unique strong core allocation (Roth–Postlewaite)
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, proof of Theorem 1, p.13: "We can also assume that iR̃ⱼxⱼ. (Otherwise xⱼP̃ⱼi and hence, from the TTC algorithm, x̃ = x.)"

import Mathlib
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_SamePref
import Definitions.Def_HousingRI_IsStrongCore
import Definitions.Def_HousingRI_IsImprovement

namespace HousingRI

/-- **The case `xⱼ P̃ⱼ i`** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, proof of
Theorem 1, p.13): "We can also assume that iR̃ⱼxⱼ. (Otherwise xⱼP̃ⱼi and hence, from the TTC
algorithm, x̃ = x.)"

Let `R` and `R̃` be strict, `R̃` an improvement for `i` with respect to `R`, and suppose only agent
`j ≠ i` may have changed preferences. If `x` is the strong core allocation of `R` and agent `j`
strictly prefers `xⱼ` to `i` at `R̃`, then `x` is in the strong core at `R̃` and is the only
allocation there, i.e. `x̃ = x`.

**Formalization Note.** Preferences are utility matrices; "R̃ₖ = Rₖ for k ≠ j" is the ordinal
`SamePref A Ã k`. `IsImprovement` is the corrected definition (conditions (1)–(4)). -/
theorem strongCore_unchanged_of_not_improved {N : Type*} [Fintype N] (i j : N)
    (A Ã : N → N → ℝ) (hA : IsStrict A) (hÃ : IsStrict Ã) (himp : IsImprovement i A Ã)
    (hji : j ≠ i) (hsame : ∀ k, k ≠ j → SamePref A Ã k) (x : N → N) (hx : IsStrongCore A x)
    (hjx : Ã j i < Ã j (x j)) :
    IsStrongCore Ã x ∧ ∀ x' : N → N, IsStrongCore Ã x' → x' = x := by sorry

end HousingRI
