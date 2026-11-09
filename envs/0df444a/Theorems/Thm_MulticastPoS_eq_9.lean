-- Prove2me | Theorems.Thm_MulticastPoS_eq_9
-- name    : MulticastPoS.eq_9
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T06:40:49.176291+00:00
-- url     : https://prove2.me/theorems/d18a4661-70e6-4a6d-8d8a-30b621fa931d
-- title:
--   Eq. (9) — $\Phi(P^{(K)})\le\sum_f c_fH_{A_f}+\sum_e c_eH_{D_e}$, with $H_{a+b}\le H_a+H_b$
-- statement:
--   1. For all nonnegative integers $a,b$, $H_{a+b}\le H_a+H_b$.
--   2. Let the edge costs be nonnegative and let every player $i$ have a raw walk $L_iD_i$ from $s_i$ to $t$. Every profile $R$ that uses only edges of the raw walks satisfies
--
--   $$
--   \Phi(R)\le\sum_{f} c_f H_{A_f}+\sum_{f} c_f H_{D_f}, \tag{9}
--   $$
--
--   where $A_f$ and $D_f$ count the players whose local segment $L_i$, respectively copied tail $D_i$, uses $f$.
--
--   This separates the new potential into the local-segment part (Lemma 5.2) and the copied-tail part (Corollary 5.5).
--
--   **Formalization Note** Both sums run over all edges; off the graph both counts are $0$ and $H_0=0$.
--
--   Differences from the source:
--   - encoding: finite undirected graph G = (V, E); player i chooses a simple path P_i from s_i to t; n players → SimpleGraph on a Fintype V; strategies are the edge sets p.edges.toFinset of walks p : G.Walk (s i) t with p.IsPath; players a Fintype ι; reason: the same games: loops never lie on a simple path, a parallel edge is equivalent to a subdivided edge with costs c_e and 0 (same strategies, payments, potential and social cost), and payments, loads, Φ and SC depend on a path only through its edge set
--   - encoding: a nonnegative cost c_e on each edge e → c : Sym2 V → ℝ with 0 ≤ c e for every e ∈ G.edgeSet; reason: the values of c off the graph never enter: no strategy contains a non-edge
--   - generalization: Φ(P^(K)) for the loop-erased profile of a representative selection, local segments and copied tails → Φ(R) for every profile R inside the raw walks of any family of walks L_i : s_i → m_i, D_i : m_i → t; reason: the paper's profile is such an R (Lemma 5.1)
--   - encoding: second sum over e ∈ T → second sum over all edges; reason: copied tails use only edges of T, so D_e = 0 off T and the two sums agree in the paper's setting
-- source:
--   Huang–Yuan, An O(log log n) Upper Bound on the Price of Stability for Undirected Multicast Shapley Games, STOC 2027 submission (manuscript sha256 dd0e08d0…), Section 5.1, p.9 (PDF p.10), Eq. (9)

import Mathlib
import Definitions.Def_MulticastPoS_game
import Definitions.Def_MulticastPoS_walkCount

open CongestionPoA.AsymSum PriceOfStability.Harmonic

namespace MulticastPoS

/-- Eq. (9) and the subadditivity of harmonic numbers (Huang–Yuan, *An O(log log n) Upper Bound
on the Price of Stability for Undirected Multicast Shapley Games*, STOC 2027 submission
manuscript (sha256 dd0e08d0…f6d4), Section 5.1, p.9):

1. `H_{a+b} ≤ H_a + H_b` for all nonnegative integers `a, b`;
2. with nonnegative edge costs, every profile `R` that uses only edges of the raw walks
   `Lᵢ Dᵢ` satisfies `Φ(R) ≤ Σ_f c_f H_{A_f} + Σ_f c_f H_{D_f}`, where `A_f`, `D_f` count the
   players whose local segment `Lᵢ`, resp. copied tail `Dᵢ`, uses `f`.

**Formalization Note** Harmonic numbers are Mathlib's `harmonic : ℕ → ℚ` (`H₀ = 0`) cast to `ℝ`.
Both sums run over all of `Sym2 V`: off the graph both counts are `0` and `H₀ = 0`. The paper's
second sum is over `e ∈ T`, which is the same sum because copied tails use only edges of `T`. -/
theorem eq_9 :
    (∀ a b : ℕ, (harmonic (a + b) : ℝ) ≤ harmonic a + harmonic b) ∧
    (∀ {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
      (G : SimpleGraph V) (c : Sym2 V → ℝ) (t : V) (s m : ι → V),
      (∀ e ∈ G.edgeSet, 0 ≤ c e) →
      ∀ (L : ∀ i, G.Walk (s i) (m i)) (D : ∀ i, G.Walk (m i) t) (R : ι → Finset (Sym2 V)),
      (∀ i, R i ⊆ ((L i).edges ++ (D i).edges).toFinset) →
      potential (game G c t s) R ≤
        (∑ f, c f * (harmonic (walkCount L f) : ℝ)) +
          (∑ f, c f * (harmonic (walkCount D f) : ℝ))) := by sorry

end MulticastPoS
