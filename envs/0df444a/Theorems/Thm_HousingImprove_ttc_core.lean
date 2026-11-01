-- Prove2me | Theorems.Thm_HousingImprove_ttc_core
-- name    : HousingImprove.ttc_core
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:29:04.129257+00:00
-- url     : https://prove2.me/theorems/918e3258-85d8-4a42-9056-20d18b661a31
-- title:
--   TTC for partial orders yields a core allocation
-- statement:
--   Let $H$ be a housing market with partial-order preferences on a finite agent set.
--
--   1. $H$ has an allocation in its core. This includes the market with no agents.
--   2. If $H$ is a market on the agents $\{0,\dots,n-1\}$ presented by its Hasse diagrams $I$, then for every set $W$ of agents the program `ttcProg` run on $W$ returns an allocation $X_W$ of the submarket $H_W$ that lies in the core of $H_W$.
--
--   The TTC variant for partial orders computes the allocation $X_R$ of the irrelevant agents in Algorithm HM-Improve (line 19), where the set of irrelevant agents may be empty. Part 1 is the form used on an arbitrary finite agent set.
--
--   Differences from the source:
--   - encoding: an allocation is a set X ⊆ E with δ⁻_X(a) = δ⁺_X(a) = 1, and X is in the core if G^H_{X≺} is acyclic → Equiv.Perm N with every X(a) acceptable to a; the core as ¬TransGen of the X-augmenting relation at every agent; reason: same objects
--   - encoding: a housing market on a finite agent set N → [Fintype N]; reason: same instances
--   - encoding: given H, H′ and X (and p) → Hasse-diagram presentations I of H and I′ of H′ (vertex, out- and in-neighbour lists), X as a function, p; reason: the input format of Appendix A, p.30; Represents ties each presentation to its market
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Appendix A, pp.29–30 ("A simple approach is to select a set of mutually vertex-disjoint cycles …", p.30; "this algorithm always finds an allocation in the core", p.29)

import Mathlib
import Definitions.Def_HousingImprove_ttcProg

namespace HousingImprove

universe u

/-- **TTC for partial orders yields a core allocation** (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, Appendix A, pp.29–30): "A simple approach is to select a set of mutually
vertex-disjoint cycles in each round, removing the agents trading along them from the market and
proceeding with the remainder in the same manner. It is not hard to see that this approach yields
an algorithm that produces an allocation in the core".

(1) Every housing market on a finite agent set, including the empty one, has an allocation in its
core. (2) For every market `H` on `Fin n` presented by `I` and every agent set `W`, the program
`ttcProg` (the implementation of p.30) run on `W` returns an allocation in the core of the
submarket `H_W`.

**Formalization Note.** Part (1) is the form used for the submarket `H'_{R∩N}` of Algorithm 1,
line 19, on an arbitrary finite type; part (2) is the algorithm itself. Its running time is
`ttc_linear_time`. -/
theorem ttc_core :
    (∀ {N : Type u} [Fintype N] (H : Market N), ∃ X : Equiv.Perm N, H.IsCore X) ∧
    (∀ (n : ℕ) (H : Market (Fin n)) (I : HassePres n) (W : Finset (Fin n)),
      Represents I H →
      ∃ XW : Equiv.Perm (W : Set (Fin n)),
        (∀ a : (W : Set (Fin n)), (ttcProg I fun b => decide (b ∈ W)).run' 0 a = (XW a).1) ∧
        (H.restrict (W : Set (Fin n))).IsCore XW) := by sorry

end HousingImprove
