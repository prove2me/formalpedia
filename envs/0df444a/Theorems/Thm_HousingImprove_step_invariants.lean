-- Prove2me | Theorems.Thm_HousingImprove_step_invariants
-- name    : HousingImprove.step_invariants
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:28:32.923163+00:00
-- url     : https://prove2.me/theorems/4f9d48be-069a-4c8e-ac68-e787fdd74e4e
-- title:
--   HM-Improve keeps a sub-allocation whose sinks are new agents (corrected: clause (iii) of an improvement; no loop at a sink)
-- statement:
--   Let $X$ be an allocation in the core of a housing market $H$ on a finite agent set and let $H'$ be a $p$-improvement of $H$. For every state $(Y,R)$ reached by a run of HM-Improve:
--
--   1. $Y$ is a sub-allocation of $\widetilde H-R$;
--   2. the sink set $V$ of $Y$ is contained in $\widetilde Q$;
--   3. if the source set of $Y$ differs from its sink set, one of Steps 2(a), 2(b), 3 applies.
--
--   So the iteration never gets stuck before $U=V$.
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
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, p.12 ("It will maintain the property that Y is a sub-allocation in H̃ − R; … the sink set always remains a subset of Q̃.")

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_Step

namespace HousingImprove

universe u

/-- **Every step keeps a sub-allocation whose sinks are new agents** (Schlotter, Biró, Fleiner,
arXiv:2110.06875v3, §4.1, p.12): "It will maintain the property that `Y` is a sub-allocation in
`H̃ − R`; we denote its envy graph by `G̃_{Y≺}`, having vertex set `Ñ \ R`. While the source set of
`Y` changes quite freely during the iteration, the sink set always remains a subset of `Q̃`."

For every state reached by a run of HM-Improve: `Y` is a sub-allocation of `H̃ − R`, its sink set
lies in `Q̃`, and if the source set differs from the sink set, an iteration (Step 2 or Step 3)
applies.

**Formalization Note.** The last clause is the page's implicit claim that Steps 1–3 cover every case
(with `|U| = |V|`, `U ≠ V` leaves a vertex in `U \ V` for Step 3).

`Q` is every set the page allows (`IsQChoice`): the agents of a series `q₁, …, q_k` of
`(p, q_i)`-improvements that prefer `p`'s house to `X(q_i)` in `H'`, Algorithm 1's
`{a : ≺_a ≠ ≺'_a, X(a) ≺'_a p}` included. -/
theorem step_invariants {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) (s : HMState Q) (hs : HMReachable H' X p Q s) :
    IsSubAllocation (tildeMarket H' p Q) s.alive s.Y ∧
    s.V ⊆ Set.range Sum.inr ∧
    (¬ s.IsTerminal → ∃ s', HMStep H' p Q s s') := by sorry

end HousingImprove
