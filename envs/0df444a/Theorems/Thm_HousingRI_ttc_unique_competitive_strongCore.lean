-- Prove2me | Theorems.Thm_HousingRI_ttc_unique_competitive_strongCore
-- name    : HousingRI.ttc_unique_competitive_strongCore
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:40.793385+00:00
-- url     : https://prove2.me/theorems/c1f98806-3f99-42d6-9c44-2eba4c19c981
-- title:
--   The top trading cycles outcome is the unique competitive and the unique strong core allocation
-- statement:
--   Let $N$ be a finite set of agents; agent $i$ owns object $i$, so $N$ is also the set of objects. Preferences are given by a real matrix $A$: agent $i$ weakly prefers object $j$ to object $k$ ($j\,R_i\,k$) when $A_{ik}\le A_{ij}$, strictly ($j\,P_i\,k$) when $A_{ik}<A_{ij}$. Object $j$ is acceptable to $i$ when $A_{ii}\le A_{ij}$.
--
--   Run the top trading cycles algorithm: repeatedly every remaining agent points to the owner of her most preferred remaining object, a cycle of this pointing graph trades and leaves. Record the run as a partition of $N$ into successive top trading cycles $S^1,\dots,S^p$ with successor map $\mathrm{next}$, and let $x_i=\mathrm{next}(i)$.
--
--   If preferences are strict, then for every such run
--
--   1. $x$ is the unique competitive allocation: an allocation $y$ is competitive for some real price vector if and only if $y=x$, and
--   2. $x$ is the unique strong core allocation: $y$ is in the strong core if and only if $y=x$.
--
--   This identifies $\tau(R)$ with the outcome of the algorithm, which is how the proof of Theorem 1 computes it.
--
--   **Formalization Note** A run is the published `ShapleyScarf.TopTrading.TTCPartition A`, which exists for every profile (`exists_ttcPartition`, Proved); its competitiveness at cycle prices is the Proved `ttc_core_and_competitive`.
--
--   Differences from the source:
--   - generalization: N = {1, …, n} with n ≥ 2 → any finite type `N`; reason: the statement specializes to `N = Fin n`, n ≥ 2
--   - encoding: complete transitive preferences Rᵢ over objects → utility matrix `A : N → N → ℝ` with j Rᵢ k iff `A i k ≤ A i j`; only the order of each row is used; reason: every complete transitive relation on a finite set has a real utility representation; same instances
--   - encoding: allocation x ∈ N^N with ∪ᵢ{xᵢ} = N → bijection `x : N → N`; reason: for finite N a surjective self-map is a bijection; same instances
--   - encoding: condition (1) of "S weakly blocks x": {zᵢ : i ∈ S} = S → `∀ i ∈ S, z i ∈ S` with z a bijection; reason: for a bijection of a finite set the two are equivalent
--   - encoding: competitive equilibrium (x, p): p_{xᵢ} ≤ pᵢ and j Pᵢ xᵢ ⟹ pⱼ > pᵢ → published `ShapleyScarf.TopTrading.IsCompetitive A x price` with real prices: `price (x i) ≤ price i` and `price k ≤ price i → A i k ≤ A i (x i)`; reason: the second clause is the contrapositive of (ii); same instances
--   - encoding: the set of cycles E^C produced by the TTC algorithm → the successor map `P.next` of a top-trading-cycle partition `P : TTCPartition A`; reason: under strict preferences each stage's top trading cycle is the cycle the algorithm removes; same allocation
-- source:
--   Biró, Klijn, Klimentova, Viana, Shapley-Scarf Housing Markets: Respecting Improvement, Integer Programming, and Kidney Exchange, arXiv:2102.00167v1, §2.1, p.10: "When the algorithm terminates the set of cycles in E^C is the unique competitive allocation and hence the unique strong core allocation."

import Mathlib
import Definitions.Def_ShapleyScarf_TopTrading_Market
import Definitions.Def_ShapleyScarf_TopTrading_TopTradingCycle
import Definitions.Def_HousingRI_IsStrict
import Definitions.Def_HousingRI_IsStrongCore

namespace HousingRI

open ShapleyScarf.TopTrading

/-- **The TTC outcome** (Biró, Klijn, Klimentova, Viana, arXiv:2102.00167v1, §2.1, p.10): "When
the algorithm terminates the set of cycles in E^C is the unique competitive allocation and hence
the unique strong core allocation."

For a market with strict preferences and every top-trading-cycle partition `P`, the allocation
`P.next` (each agent receives the object of her successor in her trading cycle) is the unique
competitive allocation and the unique strong core allocation.

**Formalization Note.** The run of the TTC algorithm is the published
`ShapleyScarf.TopTrading.TTCPartition A` (stage `t` is the cycle `c_t` removed at step `t`,
every member pointing to a most preferred remaining object); its existence is the Proved
`ShapleyScarf.TopTrading.exists_ttcPartition`. Under strict preferences the most preferred
remaining object is unique (the agent's own object remains while she does), so `P.next` is the
cycle set `E^C`. -/
theorem ttc_unique_competitive_strongCore {N : Type*} [Fintype N] [DecidableEq N]
    (A : N → N → ℝ) (hA : IsStrict A) (P : TTCPartition A) :
    (∀ y : N → N, (∃ price : N → ℝ, IsCompetitive A y price) ↔ y = P.next) ∧
      ∀ y : N → N, IsStrongCore A y ↔ y = P.next := by sorry

end HousingRI
