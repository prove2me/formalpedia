-- Prove2me | Theorems.Thm_NestedCRP_ncrp_hasSum_one
-- name    : NestedCRP.ncrp_hasSum_one
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:28:30.558389+00:00
-- url     : https://prove2.me/theorems/c9f54156-db81-4aaf-882b-75ba497bea67
-- title:
--   The nested CRP is a probability law on trees
-- statement:
--   For $\gamma>0$ and $D$ tourists, every tree separating all tourists at a finite level has positive nested CRP mass, and
--
--   $$
--   \sum_{T}\mathrm{ncrp}(T)=1.
--   $$
--
--   Moreover, in every such tree each node has at most $D$ children: for every level $\ell$ and tourist $d$, the level-$(\ell+1)$ blocks of the members of $d$'s level-$\ell$ node number at most $D$.
--
--   So the $D$ tourists trace a random subtree with branching factor at most $D$ (the page's $M$), and with probability one they have all separated at a finite level. This sum justifies taking the separated trees as the state space.
--
--   Differences from the source:
--   - reading: the collection of paths describes a random subtree, with no normalization stated → all masses positive and summing to 1 on trees separated at a finite level; reason: the sentence presupposes a probability law; this says it is one, and the separation holds almost surely
--   - encoding: infinite paths through the infinite tree of restaurants → nested partitions of the tourists; reason: the paper's own "nested sequence of partitions" (p.7:9); same law on the unlabelled tree
-- source:
--   Blei–Griffiths–Jordan, The nested Chinese restaurant process and Bayesian nonparametric inference of topic hierarchies, J. ACM 57(2), Article 7 (2010), https://doi.org/10.1145/1667053.1667056, §3, p.7:9

import Mathlib
import Definitions.Def_NestedCRP_ncrpMass

namespace NestedCRP

/-- The nCRP on `D` tourists is a probability law on trees that separate all tourists at a finite
level: every such tree has positive mass, and the masses sum to one. Every node of such a tree has
at most `D` children ("this subtree has a branching factor of at most M at all nodes").
Blei–Griffiths–Jordan, *The nested Chinese restaurant process and Bayesian nonparametric
inference of topic hierarchies*, J. ACM 57(2), Article 7 (2010), §3, p.7:9.

**Formalization Note** This sum is what justifies the separation clause of `Tree`. The paper's `M`
is `D`. The children of the node of `d` at level `ℓ` are the level-`ℓ + 1` blocks of its members. -/
theorem ncrp_hasSum_one {D : ℕ} {γ : ℝ} (hγ : 0 < γ) :
    (∀ T : Tree D, 0 < ncrpMass γ T) ∧ HasSum (ncrpMass γ : Tree D → ℝ) 1 ∧
      ∀ (T : Tree D) (ℓ : ℕ) (d : Fin D),
        ((T.block ℓ d).image (T.block (ℓ + 1))).card ≤ D := by sorry

end NestedCRP
