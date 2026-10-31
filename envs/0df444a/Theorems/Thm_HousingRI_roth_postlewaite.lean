-- Prove2me | Theorems.Thm_HousingRI_roth_postlewaite
-- name    : HousingRI.roth_postlewaite
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:41.241194+00:00
-- url     : https://prove2.me/theorems/5538b587-adce-4041-ab0d-0cc28e7b840f
-- title:
--   Roth–Postlewaite: under strict preferences the strong core is a single allocation, the unique competitive allocation
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$. Allocations are bijections $x:N\to N$. A price vector $p\in\mathbb R^N$ supports $x$ as a **competitive equilibrium** if for each agent $i$ the allotment is affordable, $p_{x_i}\le p_i$, and every object $j$ with $j\,P_i\,x_i$ costs more, $p_j>p_i$; $x$ is a competitive allocation if some $p$ does.
--
--   If preferences are strict (no ties between acceptable objects), then
--
--   1. there is exactly one allocation in the strong core, and
--   2. an allocation is competitive if and only if it is in the strong core,
--
--   so the unique strong core allocation coincides with the unique competitive allocation. This is the statement that makes $\tau(R)$ in Theorem 1 well defined.
--
--   **Formalization Note** Competitiveness is the published `ShapleyScarf.TopTrading.IsCompetitive`, whose second clause is the contrapositive of the page's (ii).
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type `N`; reason: the statement specializes to `N = Fin n`, n ≥ 2
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - encoding: allocation x ∈ N^N with ∪ᵢ{xᵢ} = N → bijection `x : N → N`; reason: for finite N a surjective self-map is a bijection; same instances
--   - encoding: condition (1) of "S weakly blocks x": {zᵢ : i ∈ S} = S → `∀ i ∈ S, z i ∈ S` with z a bijection; reason: for a bijection of a finite set the two are equivalent
--   - encoding: competitive equilibrium (x, p): p_{xᵢ} ≤ pᵢ and j Pᵢ xᵢ ⟹ pⱼ > pᵢ → published `ShapleyScarf.TopTrading.IsCompetitive A x price` with real prices: `price (x i) ≤ price i` and `price k ≤ price i → A i k ≤ A i (x i)`; reason: the second clause is the contrapositive of (ii); same instances
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §2, p.9: "Roth and Postlewaite [36] showed that if preferences are strict, then there is a unique strong core allocation which coincides with the unique competitive allocation."

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_IsStrongCore

namespace HousingRI

open ShapleyScarf.TopTrading

/-- **Roth–Postlewaite** (quoted in Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, §2, p.9):
"Roth and Postlewaite [36] showed that if preferences are strict, then there is a unique strong
core allocation which coincides with the unique competitive allocation."

Both clauses: under strict preferences the strong core is a singleton, and an allocation is
competitive (for some real price vector) if and only if it is in the strong core.

**Formalization Note.** `N` is any finite type (the paper: `N = {1,…,n}`, `n ≥ 2`).
Preferences are a utility matrix with strictness only among acceptable objects (`IsStrict`).
Competitiveness is the published `ShapleyScarf.TopTrading.IsCompetitive` (allocation a
bijection, `p_{xᵢ} ≤ pᵢ`, and every object priced at most `pᵢ` is weakly worse than `xᵢ`, the
contrapositive of p.7 (ii)). -/
theorem roth_postlewaite {N : Type*} [Fintype N] (A : N → N → ℝ) (hA : IsStrict A) :
    (∃! x : N → N, IsStrongCore A x) ∧
      ∀ x : N → N, (∃ price : N → ℝ, IsCompetitive A x price) ↔ IsStrongCore A x := by sorry

end HousingRI
