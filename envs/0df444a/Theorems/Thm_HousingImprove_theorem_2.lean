-- Prove2me | Theorems.Thm_HousingImprove_theorem_2
-- name    : HousingImprove.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:31:24.740914+00:00
-- url     : https://prove2.me/theorems/2294c9ed-cae2-4264-bc7e-1c52ce97b5f7
-- title:
--   Theorem 2 — the core respects improvement, and an allocation proving it is found in $O(|H|)$ time (corrected: no house moves above $p$)
-- statement:
--   Let $H=(N,\{\prec_a\}_{a\in N})$ be a housing market with partial-order preferences on a finite agent set, let $X$ be an allocation in the core of $H$, and let $H'$ be a $p$-improvement of $H$: other agents come to value the house of $p$ more, while the order among the other houses and the preferences of $p$ stay the same.
--
--   1. There exists an allocation $X'$ in the core of $H'$ such that
--   $$X(p)=X'(p)\quad\text{or}\quad X(p)\prec_p X'(p),$$
--   i.e. $p$ obtains the same house as in $X$ or one she prefers.
--   2. Such an allocation can be found in linear time: there is a constant $C$ such that, for every such instance on the agents $\{0,\dots,n-1\}$ given by the Hasse diagrams $I$ of $H$ and $I'$ of $H'$, the program `hmImproveProg I I' X p` (Algorithm HM-Improve) returns an allocation $X'$ as in part 1 and performs at most $C\cdot|H|$ unit operations, where $|H|=\sum_a|H_a|$.
--
--   In particular the core of housing markets satisfies the respecting-improvement property for the best available house (Corollary 1): an agent never loses by bringing a better house to the market.
--
--   **Formalization Note** The time bound is in the length of the description of $H$; the program reads $H'$ only at $p$, since $|H'|$ can be of order $|H|^2$.
--
--   Differences from the source:
--   - correction: a (p,q)-improvement satisfies (i) a ≺′_q b ⇔ a ≺_q b for a, b ≠ p, and (ii) a ≺_q p ⇒ a ≺′_q p (p.9) → IsImprovementAt adds clause (iii): p ≺′_q a ⇒ p ≺_q a for every a; reason: with (i) and (ii) only, Theorem 2 is false: N = {p, q, a}, p ranks q above a above p, a ranks q above a with p unacceptable, q has p and a incomparable above q in H and a above p above q in H′; the swap (p q) is in the core of H and every core allocation of H′ gives p the house of a or her own (proved in the verification file); for strict orders (iii) follows from (ii)
--   - reading: a (p,q)-improvement for agents p and q (q = p not excluded) → q ≠ p; reason: p.12 says the preferences of p remain unchanged; with q = p the theorem fails (N = {p, b}, p raises her own house above b's: the swap is in the core of H, the only core allocation of H′ gives p her own house)
--   - reading: a sequence of (p,q_i)-improvements for some k ∈ ℕ → a list of any length, k = 0 (H′ = H) included; reason: whether 0 ∈ ℕ is not fixed by the paper; for k = 0 every statement holds with X′ = X
--   - encoding: an allocation is a set X ⊆ E with δ⁻_X(a) = δ⁺_X(a) = 1, and X is in the core if G^H_{X≺} is acyclic → Equiv.Perm N with every X(a) acceptable to a; the core as ¬TransGen of the X-augmenting relation at every agent; reason: same objects
--   - encoding: a housing market on a finite agent set N → [Fintype N]; reason: same instances
--   - reading: |H| (not defined in Theorem 2) → HassePres.size: Σ_a (vertices + arcs of the Hasse diagram H_a); reason: Appendix A, p.30 defines |H| = Σ_a |H_a|; |H_a| counts vertices and arcs, as the bound O(|N| + Σ_a |H_a|) = O(|H|) on p.30 needs
--   - reading: O(|H|) time → one universal constant C, placed before the instance, bounding the number of unit operations of the concrete charged program; reason: unit-cost RAM; the program is a specific definition under the charging discipline of Prog, so the bound cannot be met by a cost-free Lean function
--   - encoding: given H, H′ and X (and p) → Hasse-diagram presentations I of H and I′ of H′ (vertex, out- and in-neighbour lists), X as a function, p; reason: the input format of Appendix A, p.30; Represents ties each presentation to its market
--   - reading: O(|H|) for inputs H, H′, X → the bound is C · |H| with |H| the size of I, not of I′; reason: the literal statement; |H′| can be of order |H|², and hmImproveProg reads I′ only at p
--   - encoding: p prefers X′ to X → X(p) ≺_p X′(p) in H; reason: p's preferences are the same in H and H′
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Theorem 2, p.10 (proved on p.19 from Lemmas 3, 4 and Proposition 2)

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_hmImproveProg

namespace HousingImprove

universe u

/-- **Theorem 2** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, p.10; proved on p.19), with the
corrected `p`-improvement: "For any allocation `X` in the core of housing market `H` and a
`p`-improvement `H'` of `H`, there exists an allocation `X'` in the core of `H'` such that either
`X(p) = X'(p)` or `p` prefers `X'` to `X`. Moreover, given `H`, `H'` and `X`, it is possible to find such
an allocation `X'` in `O(|H|)` time."

(1) For every finite agent set `N`, every market `H` with partial-order preferences, every core
allocation `X` of `H` and every `p`-improvement `H'` of `H`, some allocation `X'` in the core of `H'`
has `X(p) = X'(p)` or `X(p) ≺_p X'(p)`.
(2) There is a universal constant `C` such that, for every such instance on `Fin n` presented by
Hasse diagrams `I` (of `H`) and `I'` (of `H'`), the program `hmImproveProg I I' X p` returns such an
allocation `X'` and performs at most `C · |H|` unit operations.

**Formalization Note.** A `(p, q)`-improvement carries the added clause (iii) "`p ≺'_q a` implies
`p ≺_q a`" and `q ≠ p` (`IsImprovementAt`); without (iii) the theorem is false. `|H|` is
`HassePres.size` (vertices plus arcs of the Hasse diagrams, Appendix A, p.30); time is the number of
unit operations of the charged program. -/
theorem theorem_2 :
    (∀ {N : Type u} [Fintype N] (H H' : Market N) (p : N) (X : Equiv.Perm N),
      H.IsCore X → IsPImprovement p H H' →
      ∃ X' : Equiv.Perm N, H'.IsCore X' ∧ (X p = X' p ∨ H.lt p (X p) (X' p))) ∧
    (∃ C : ℕ, ∀ (n : ℕ) (H H' : Market (Fin n)) (I I' : HassePres n) (p : Fin n)
        (X : Equiv.Perm (Fin n)),
      Represents I H → Represents I' H' → H.IsCore X → IsPImprovement p H H' →
      ∃ X' : Equiv.Perm (Fin n),
        (hmImproveProg I I' X p).run' 0 = ⇑X' ∧ H'.IsCore X' ∧ (X p = X' p ∨ H.lt p (X p) (X' p)) ∧
        ((hmImproveProg I I' X p).run 0).2 ≤ C * I.size) := by sorry

end HousingImprove
