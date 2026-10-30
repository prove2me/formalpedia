-- Prove2me | Theorems.Thm_LNTopology_Hermetization_cost_hermetize_eq
-- name    : LNTopology.Hermetization.cost_hermetize_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:29:20.030675+00:00
-- url     : https://prove2.me/theorems/646bee0d-5e14-4e94-a844-2881d5052e91
-- title:
--   Cost identity of hermetization (proof of Lemma B.1)
-- statement:
--   Let $\Lambda=(\lambda_{i,j})$ be a Lightning Network on a finite node set $V$, let the cost function $c$ satisfy (SY) $c(-x)=c(x)$ and (CI) $c(0)=0$, and let $U\subseteq V$. Write $G'_U$ for the hermetization of $U$. Then
--
--   $$c(G'_U)=c(G)-\frac12\sum_{i\in U}\sum_{j\in U}c(\lambda_{i,j})+\sum_{i\in U}c\Bigl(\sum_{j\in U}\lambda_{i,j}\Bigr).$$
--
--   Hermetization removes the channels inside $U$, whose cost is $\frac12\sum_{i,j\in U}c(\lambda_{i,j})$, and adds one channel per node $i\in U$ to the new node, carrying $\sum_{j\in U}\lambda_{i,j}$. Hence $U$ is hermetizable if and only if
--
--   $$\sum_{i\in U}c\Bigl(\sum_{j\in U}\lambda_{i,j}\Bigr)<\sum_{i\in U}\frac12\sum_{j\in U}c(\lambda_{i,j}),$$
--
--   which is how the proof of Lemma B.1 reduces hermetizability to the node-wise inequality (7).
--
--   Differences from the source:
--   - reading: the displays sum over j = 1, …, n, treating U as the whole network → U ⊆ V inside a larger network: the new channels carry Σ_{j∈U} λ_{i,j}, and the channels between U and V ∖ U are unchanged; reason: Definition 3.6 hermetizes a subset U of an LN with channels "towards other nodes in U"; at U = V the identity is the paper's display
--   - generalization: the cost function satisfies (MO)–(SA+) → only (SY) and (CI) are assumed; reason: the identity uses only these two axioms; every cost function of the paper satisfies them
--   - encoding: the new node 0; λ′_{0,l} = Σ_i λ_{i,l} → none : Option V; λ′_{v₀,l} = −Σ_{w∈U} λ_{l,w}; reason: the same number for an antisymmetric matrix; keeps λ′ antisymmetric
-- source:
--   Guasoni, Huberman, Shikhelman, Lightning Network Economics: Topology, working paper (SSRN 4439190, February 3, 2023), proof of Lemma B.1, displays before (7), p. 11 (PDF p. 12)

import Mathlib
import Definitions.Def_LNTopology_Hermetization_IsLN
import Definitions.Def_LNTopology_Hermetization_cost
import Definitions.Def_LNTopology_Hermetization_hermetize

namespace LNTopology.Hermetization

/-- **The cost identity of hermetization (proof of Lemma B.1).**
Guasoni, Huberman, Shikhelman, *Lightning Network Economics: Topology*, working paper
(SSRN 4439190, February 3, 2023), proof of Lemma B.1, displays before (7), p. 11: "c(U) = 1/2 Σ_{i,j=1}^{n,n} c(λi,j) =
Σ_{i=1}^n 1/2 Σ_{j=1}^n c(λi,j)", "c(U′) = 1/2 Σ_{i=1}^n (c(λ′i,0) + c(λ′0,i)) =
Σ_{i=1}^n c(λ′i,0) = Σ_{i=1}^n c(Σ_{j=1}^n λi,j)".

For an LN, a cost function with (SY) and (CI), and any node set `U`, hermetizing `U` removes the
cost `½ Σ_{i,j ∈ U} c(λ_{i,j})` of the channels inside `U` and adds `Σ_{i∈U} c(Σ_{j∈U} λ_{i,j})`,
the cost of the new channels to `v₀`.

**Formalization Note.** Reading R2: the paper's display treats `U` as the whole network; the
identity here is for `U ⊆ V` inside a larger network, where the channels between `U` and
`V ∖ U` are unchanged. Only (SY) and (CI) of the cost axioms are used, so only they are assumed. -/
theorem cost_hermetize_eq {V : Type*} [Fintype V] [DecidableEq V] (c : ℝ → ℝ)
    (lam : V → V → ℝ) (hLN : IsLN lam) (hSY : ∀ x : ℝ, c (-x) = c x) (hCI : c 0 = 0)
    (U : Finset V) :
    cost c (hermetize lam U) =
      cost c lam - (1 / 2) * ∑ i ∈ U, ∑ j ∈ U, c (lam i j) +
        ∑ i ∈ U, c (∑ j ∈ U, lam i j) := by sorry

end LNTopology.Hermetization
