-- Prove2me | Theorems.Thm_HousingRI_respects_improvement_one_agent
-- name    : HousingRI.respects_improvement_one_agent
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:14.685328+00:00
-- url     : https://prove2.me/theorems/3fbaf7e6-72e2-4f73-ac51-bd7f1afa67ec
-- title:
--   Proof of Theorem 1, pp.13–14 — the one-changed-agent case of Theorem 1 (corrected improvement)
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$. Allocations are bijections of $N$.
--
--   Let $R$ and $\tilde R$ be strict profiles such that $\tilde R$ is an improvement for $i$ with respect to $R$, and suppose every agent other than one agent $j\ne i$ has the same preferences at $R$ and $\tilde R$. If $x$ is in the strong core at $R$ and $\tilde x$ is in the strong core at $\tilde R$, then
--
--   $$\tilde x_i\;R_i\;x_i .$$
--
--   This is the case the proof of Theorem 1 treats directly, by a case analysis on the relation between $i$ and $j$ in the graph of the top trading cycles algorithm; the general case follows by changing one agent at a time.
--
--   **Formalization Note** Improvement is the corrected definition (conditions (1)–(4)). $x$ and $\tilde x$ range over strong core allocations, which under strict preferences are $\tau(R)$ and $\tau(\tilde R)$.
--
--   Differences from the source:
--   - correction: R̃ is an improvement for i: conditions (1)–(3), p.13 → `IsImprovement i A Ã`: (1)–(3) plus (4) for all j ≠ i and k ≠ i, k R̃ⱼ j ⟹ k Rⱼ j; reason: with (1)–(3) alone Theorem 1 is false: N = {1,2,3}, i = 1, R₁: 2 P 1 P 3, R₂: 1 P 2 P 3, R₃: 2 P 3 P 1, and R̃ = R except R̃₂: 3 P 1 P 2 satisfy (1)–(3) (object 3 is unacceptable to agent 2 at R₂); τ(R) = {(1,2),(3)}, τ(R̃) = {(1),(2,3)}, so τ₁(R) = 2 P₁ 1 = τ₁(R̃) and Theorem 1 fails
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type `N`; reason: the statement specializes to `N = Fin n`, n ≥ 2
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - encoding: allocation x ∈ N^N with ∪ᵢ{xᵢ} = N → bijection `x : N → N`; reason: for finite N a surjective self-map is a bijection; same instances
--   - encoding: condition (1) of "S weakly blocks x": {zᵢ : i ∈ S} = S → `∀ i ∈ S, z i ∈ S` with z a bijection; reason: for a bijection of a finite set the two are equivalent
--   - encoding: τ(R), the unique competitive (or strong core) allocation → arbitrary strong core allocations of the profile; reason: under strict preferences the strong core is the singleton {τ(R)} (Roth–Postlewaite, milestone `roth_postlewaite`)
--   - encoding: R̃ₖ = Rₖ → `SamePref A Ã k`: the rows of A and Ã induce the same weak order; reason: preferences are ordinal; equality of the relations is equivalence of the orders
--   - generalization: a unique agent j ≠ i with R̃ⱼ ≠ Rⱼ → every agent k ≠ j has the same preferences (j itself may also be unchanged); reason: covers the source's case and in addition the case with no changed agent
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, proof of Theorem 1, pp.13–14 (Cases I–III): "Proof. Let x = τ(R) and x̃ = τ(R̃). We can assume that there is a unique agent j ≠ i with R̃ⱼ ≠ Rⱼ and prove that x̃ᵢRᵢxᵢ."

import Mathlib
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_SamePref
import Definitions.Def_HousingRI_IsStrongCore
import Definitions.Def_HousingRI_IsImprovement

namespace HousingRI

/-- **Theorem 1 for one changed agent** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, proof
of Theorem 1, pp.13–14): "Proof. Let x = τ(R) and x̃ = τ(R̃). We can assume that there is a unique
agent j ≠ i with R̃ⱼ ≠ Rⱼ and prove that x̃ᵢRᵢxᵢ."

Let `R` and `R̃` be strict, `R̃` an improvement for `i` with respect to `R`, and suppose every agent
other than one agent `j ≠ i` has the same preferences at `R` and `R̃`. If `x` is in the strong
core at `R` and `x̃` is in the strong core at `R̃`, then `x̃ᵢ Rᵢ xᵢ`.

**Formalization Note.** Preferences are utility matrices (`x̃ᵢ Rᵢ xᵢ` is
`A i (x i) ≤ A i (x̃ i)`); "R̃ₖ = Rₖ" is the ordinal `SamePref A Ã k`. `τ(R)` is the unique strong
core allocation (Roth–Postlewaite), so the statement quantifies over strong core allocations.
`IsImprovement` is the corrected definition (conditions (1)–(4)). -/
theorem respects_improvement_one_agent {N : Type*} [Fintype N] (i j : N) (A Ã : N → N → ℝ)
    (hA : IsStrict A) (hÃ : IsStrict Ã) (himp : IsImprovement i A Ã) (hji : j ≠ i)
    (hsame : ∀ k, k ≠ j → SamePref A Ã k) (x x' : N → N) (hx : IsStrongCore A x)
    (hx' : IsStrongCore Ã x') :
    A i (x i) ≤ A i (x' i) := by sorry

end HousingRI
