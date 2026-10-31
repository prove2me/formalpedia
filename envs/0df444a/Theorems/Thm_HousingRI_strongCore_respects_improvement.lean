-- Prove2me | Theorems.Thm_HousingRI_strongCore_respects_improvement
-- name    : HousingRI.strongCore_respects_improvement
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:28.721992+00:00
-- url     : https://prove2.me/theorems/81fae4cf-1a7f-42c1-93ed-ee898490a97c
-- title:
--   Theorem 1 — under strict preferences the strong core allocation respects improvement (corrected: no new acceptable objects other than $i$)
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$. Allocations are bijections $x:N\to N$. For a profile $R$ with strict preferences (no ties between acceptable objects) let $\tau(R)$ be its unique strong core allocation, which is also its unique competitive allocation and the outcome of the top trading cycles algorithm.
--
--   **Theorem.** For each agent $i\in N$ and each pair of strict profiles $R,\tilde R$ such that $\tilde R$ is an improvement for $i$ with respect to $R$,
--
--   $$\tau_i(\tilde R)\;R_i\;\tau_i(R).$$
--
--   Here $\tilde R$ is an improvement for $i$ when $i$'s own preferences are unchanged, every other agent ranks object $i$ weakly higher relative to her acceptable objects (strictly where it was strictly above), keeps her order among acceptable objects other than $i$, and finds no new object other than $i$ acceptable.
--
--   In words: when other agents come to like agent $i$'s object more, agent $i$ is never hurt by the top trading cycles mechanism. In kidney exchange this says that a patient whose donor becomes more compatible with other patients does not receive a worse kidney.
--
--   **Formalization Note** The statement quantifies over all strong core allocations $x$ of $R$ and $\tilde x$ of $\tilde R$ and concludes $A_{i x_i}\le A_{i\tilde x_i}$. Improvement includes condition (4), "no object other than $i$ becomes acceptable to any $j\ne i$", which is not printed on p.13 but without which the theorem is false.
--
--   Differences from the source:
--   - correction: R̃ is an improvement for i: conditions (1)–(3), p.13 → `IsImprovement i A Ã`: (1)–(3) plus (4) for all j ≠ i and k ≠ i, k R̃ⱼ j ⟹ k Rⱼ j; reason: with (1)–(3) alone Theorem 1 is false: N = {1,2,3}, i = 1, R₁: 2 P 1 P 3, R₂: 1 P 2 P 3, R₃: 2 P 3 P 1, and R̃ = R except R̃₂: 3 P 1 P 2 satisfy (1)–(3) (object 3 is unacceptable to agent 2 at R₂); τ(R) = {(1,2),(3)}, τ(R̃) = {(1),(2,3)}, so τ₁(R) = 2 P₁ 1 = τ₁(R̃) and Theorem 1 fails
--   - encoding: τ(R), the unique competitive (or strong core) allocation → arbitrary strong core allocations of the profile; reason: under strict preferences the strong core is the singleton {τ(R)} (Roth–Postlewaite, milestone `roth_postlewaite`)
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type `N`; reason: the statement specializes to `N = Fin n`, n ≥ 2
--   - encoding: allocation x ∈ N^N with ∪ᵢ{xᵢ} = N → bijection `x : N → N`; reason: for finite N a surjective self-map is a bijection; same instances
--   - encoding: condition (1) of "S weakly blocks x": {zᵢ : i ∈ S} = S → `∀ i ∈ S, z i ∈ S` with z a bijection; reason: for a bijection of a finite set the two are equivalent
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §3.1, Theorem 1, p.13 (τ defined p.13; improvement p.13, corrected).

import Mathlib
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_IsStrongCore
import Definitions.Def_HousingRI_IsImprovement

namespace HousingRI

/-- **Theorem 1** (Biró, Klijn, Klimentova, Viana, *Shapley-Scarf Housing Markets: Respecting
Improvement, Integer Programming, and Kidney Exchange*, arXiv:2102.00167v1, §3.1, p.13): "For
each i ∈ N and each pair of profiles of strict preferences R, R̃ such that R̃ is an improvement for
i with respect to R, τᵢ(R̃) Rᵢ τᵢ(R)", where τ(R) is "the unique competitive allocation (or
strong core allocation)" (p.13).

**Formalization Note.** `N` is any finite type of agents, agent `i` owning object `i`.
Preferences are utility matrices (`j Rᵢ k` is `A i k ≤ A i j`; only the order of each row
matters), strict among acceptable objects (`IsStrict`). Allocations are bijections `N → N`.
`τ(R)` is encoded through the strong core: the statement holds for every strong core allocation
`x` of `A` and `x'` of `Ã`, and by Roth–Postlewaite each is the unique one. `IsImprovement` is
the **corrected** definition: conditions (1)–(3) of p.13 plus (4) "no object other than `i`
becomes acceptable to any `j ≠ i`", without which the theorem is false (counterexample in the
docstring of `IsImprovement`). -/
theorem strongCore_respects_improvement {N : Type*} [Fintype N] (i : N) (A Ã : N → N → ℝ)
    (hA : IsStrict A) (hÃ : IsStrict Ã) (himp : IsImprovement i A Ã) (x x' : N → N)
    (hx : IsStrongCore A x) (hx' : IsStrongCore Ã x') :
    A i (x i) ≤ A i (x' i) := by sorry

end HousingRI
