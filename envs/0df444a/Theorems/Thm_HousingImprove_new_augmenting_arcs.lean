-- Prove2me | Theorems.Thm_HousingImprove_new_augmenting_arcs
-- name    : HousingImprove.new_augmenting_arcs
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T15:27:50.17116+00:00
-- url     : https://prove2.me/theorems/5da30abe-7420-42f6-9cb2-69baafa2f6a2
-- title:
--   New $X$-augmenting arcs enter $p$ (corrected: clause (iii) of an improvement)
-- statement:
--   Let $X$ be an allocation in the core of a housing market $H$ on a finite agent set, let $H'$ be a $p$-improvement of $H$, and let $Q$ be any admissible set (it contains every $a\neq p$ whose preferences changed and with $X(a)\prec'_a p$, and only agents $a\neq p$ with $X(a)\prec'_a p$). If an arc $(a,b)$ is $X$-augmenting in $H'$ but not in $H$, that is,
--   $$X(a)\prec'_a b\quad\text{and}\quad X(a)\not\prec_a b,$$
--   then $a\in Q$ and $b=p$.
--
--   Consequently every cycle of $X$-augmenting arcs of $H'$ uses an arc $(q,p)$ with $q\in Q$, which is why HM-Improve subdivides exactly these arcs.
--
--   Differences from the source:
--   - correction: a (p,q)-improvement satisfies (i) a ≺′_q b ⇔ a ≺_q b for a, b ≠ p, and (ii) a ≺_q p ⇒ a ≺′_q p (p.9) → IsImprovementAt adds clause (iii): p ≺′_q a ⇒ p ≺_q a for every a; reason: with (i) and (ii) only, Theorem 2 is false: N = {p, q, a}, p ranks q above a above p, a ranks q above a with p unacceptable, q has p and a incomparable above q in H and a above p above q in H′; the swap (p q) is in the core of H and every core allocation of H′ gives p the house of a or her own (proved in the verification file); for strict orders (iii) follows from (ii)
--   - reading: a (p,q)-improvement for agents p and q (q = p not excluded) → q ≠ p; reason: p.12 says the preferences of p remain unchanged; with q = p the theorem fails (N = {p, b}, p raises her own house above b's: the swap is in the core of H, the only core allocation of H′ gives p her own house)
--   - reading: a sequence of (p,q_i)-improvements for some k ∈ ℕ → a list of any length, k = 0 (H′ = H) included; reason: whether 0 ∈ ℕ is not fixed by the paper; for k = 0 every statement holds with X′ = X
--   - reading: Q = {q_i : X(q_i) ≺′_{q_i} p} for a series q_1, …, q_k of (p, q_i)-improvements (p.11); Algorithm 1, line 2: Q = {a ∈ N : ≺_a ≠ ≺′_a and X(a) ≺′_a p} → any Q with IsQChoice H H′ X p Q: every a ≠ p with ≺′_a ≠ ≺_a and X(a) ≺′_a p is in Q, and Q ⊆ Qset H′ X p = {a ≠ p : X(a) ≺′_a p}; reason: a series q_1, …, q_k must list every agent whose preferences changed and may list any other agent ≠ p (a trivial (p, a)-improvement), so these are exactly the sets the page allows; line 2's set is the smallest, Qset the largest
--   - encoding: an allocation is a set X ⊆ E with δ⁻_X(a) = δ⁺_X(a) = 1, and X is in the core if G^H_{X≺} is acyclic → Equiv.Perm N with every X(a) acceptable to a; the core as ¬TransGen of the X-augmenting relation at every agent; reason: same objects
--   - encoding: a housing market on a finite agent set N → [Fintype N]; reason: same instances
--   - encoding: the standing assumptions of §4.1: X in the core of H, H′ a p-improvement of H → hypotheses hX and hH; reason: same assumptions
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, §4.1, p.12 ("Observe that if an arc is an X-augmenting arc in H′ but not in H, then it must be an arc of the form (q, p) where q ∈ Q.")

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_tildeMarket

namespace HousingImprove

universe u

/-- **New augmenting arcs enter `p`** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, §4.1, p.12):
"Observe that if an arc is an `X`-augmenting arc in `H'` but not in `H`, then it must be an arc of
the form `(q, p)` where `q ∈ Q`." Here `X` is in the core of `H`, `H'` is a `p`-improvement of
`H`, and `Q` is an admissible set (`IsQChoice`).

**Formalization Note.** With the printed definition of a `(p, q)`-improvement (without clause
(iii)) the statement is false: an arc `(q, b)` with `X(q) = p` may become `X`-augmenting.

`Q` is every set the page allows (`IsQChoice`): the agents of a series `q₁, …, q_k` of
`(p, q_i)`-improvements that prefer `p`'s house to `X(q_i)` in `H'`, Algorithm 1's
`{a : ≺_a ≠ ≺'_a, X(a) ≺'_a p}` included. -/
theorem new_augmenting_arcs {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N)
    (hX : H.IsCore X) (hH : IsPImprovement p H H')
    (Q : Set N) (hQ : IsQChoice H H' X p Q) :
    ∀ a b, H'.lt a (X a) b → ¬ H.lt a (X a) b → a ∈ Q ∧ b = p := by sorry

end HousingImprove
