-- Prove2me | Theorems.Thm_HousingImprove_lemma_1
-- name    : HousingImprove.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:37.691642+00:00
-- url     : https://prove2.me/theorems/f01690d4-2246-496f-80ff-b579891f3601
-- title:
--   Lemma 1 — $Y$ is stable at each iteration (corrected: clause (iii) of an improvement; no loop at a sink)
-- statement:
--   Let $X$ be an allocation in the core of a housing market $H$ on a finite agent set and let $H'$ be a $p$-improvement of $H$. For every state $(Y,R)$ reached by a run of HM-Improve, the sub-allocation $Y$ is stable in $\widetilde H-R$: its envy graph, formed by the $Y$-augmenting arcs, is acyclic.
--
--   Differences from the source:
--   - correction: a (p,q)-improvement satisfies (i) a ≺′_q b ⇔ a ≺_q b for a, b ≠ p, and (ii) a ≺_q p ⇒ a ≺′_q p (p.9) → IsImprovementAt adds clause (iii): p ≺′_q a ⇒ p ≺_q a for every a; reason: with (i) and (ii) only, Theorem 2 is false: N = {p, q, a}, p ranks q above a above p, a ranks q above a with p unacceptable, q has p and a incomparable above q in H and a above p above q in H′; the swap (p q) is in the core of H and every core allocation of H′ gives p the house of a or her own (proved in the verification file); for strict orders (iii) follows from (ii)
--   - reading: a (p,q)-improvement for agents p and q (q = p not excluded) → q ≠ p; reason: p.12 says the preferences of p remain unchanged; with q = p the theorem fails (N = {p, b}, p raises her own house above b's: the swap is in the core of H, the only core allocation of H′ gives p her own house)
--   - reading: a sequence of (p,q_i)-improvements for some k ∈ ℕ → a list of any length, k = 0 (H′ = H) included; reason: whether 0 ∈ ℕ is not fixed by the paper; for k = 0 every statement holds with X′ = X
--   - reading: Q = {q_i : X(q_i) ≺′_{q_i} p} for a series q_1, …, q_k of (p, q_i)-improvements (p.11); Algorithm 1, line 2: Q = {a ∈ N : ≺_a ≠ ≺′_a and X(a) ≺′_a p} → any Q with IsQChoice H H′ X p Q: every a ≠ p with ≺′_a ≠ ≺_a and X(a) ≺′_a p is in Q, and Q ⊆ Qset H′ X p = {a ≠ p : X(a) ≺′_a p}; reason: a series q_1, …, q_k must list every agent whose preferences changed and may list any other agent ≠ p (a trivial (p, a)-improvement), so these are exactly the sets the page allows; line 2's set is the smallest, Qset the largest
--   - generalization: the iteration starts only when X is not in the core of H′ (p.11, Algorithm 1, line 1) → every run from hmInit, whether or not X is in the core of H′; reason: the proofs of §4.2 never use that X is not in the core of H′; the source's runs are among the runs covered
--   - correction: (a, b) ∈ E is Y-augmenting if a ∈ V or Y(a) ≺_a b (p.11) → (a ∈ V and b ≠ a) or Y(a) ≺_a b; reason: (a, a) ∈ E for every a, so the literal definition puts a loop at every sink and no sub-allocation with a sink is stable, which makes Lemma 1 false; its proof and Step 2 use no loop
--   - encoding: H̃ keeps the preferences of H′ (with q̃ in the place of p for q) → tildeMarket keeps them among acceptable houses; houses unacceptable to an agent are below every acceptable one and mutually incomparable; reason: the acceptability graph G̃ is exactly the page's; every statement compares acceptable houses only
--   - encoding: the algorithm HM-Improve with its free choices → every chain of HMStep transitions from hmInit (HMReachable); reason: one transition per choice the page leaves free; each run of the page is such a chain
--   - encoding: an allocation is a set X ⊆ E with δ⁻_X(a) = δ⁺_X(a) = 1, and X is in the core if G^H_{X≺} is acyclic → Equiv.Perm N with every X(a) acceptable to a; the core as ¬TransGen of the X-augmenting relation at every agent; reason: same objects
--   - encoding: a housing market on a finite agent set N → [Fintype N]; reason: same instances
--   - encoding: the standing assumptions of §4.1: X in the core of H, H′ a p-improvement of H → hypotheses hX and hH; reason: same assumptions
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Lemma 1, p.16

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_Step

namespace HousingImprove

universe u

/-- **Lemma 1** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, p.16): "At each iteration,
sub-allocation `Y` is stable in `H̃ − R`."

For `X` in the core of `H` and a `p`-improvement `H'` of `H`, every state reached by a run of
HM-Improve has an acyclic envy graph.

**Formalization Note.** `Y`-augmenting arcs exclude the loop at a sink (`IsAugmenting`); with the
loop, no sub-allocation with a sink would be stable.

`Q` is every set the page allows (`IsQChoice`): the agents of a series `q₁, …, q_k` of
`(p, q_i)`-improvements that prefer `p`'s house to `X(q_i)` in `H'`, Algorithm 1's
`{a : ≺_a ≠ ≺'_a, X(a) ≺'_a p}` included. -/
theorem lemma_1 {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) (s : HMState Q) (hs : HMReachable H' X p Q s) :
    IsStable (tildeMarket H' p Q) s.alive s.Y := by sorry

end HousingImprove
