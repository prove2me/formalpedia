-- Prove2me | Theorems.Thm_HousingImprove_lemma_4
-- name    : HousingImprove.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T15:30:36.807842+00:00
-- url     : https://prove2.me/theorems/c5015236-de27-48be-99f2-b625bc1357c8
-- title:
--   Lemma 4 — HM-Improve runs in $O(|H|)$ time (corrected: clause (iii) of an improvement; no loop at a sink)
-- statement:
--   There is a constant $C$ such that the following holds for every housing market $H$ on the agents $\{0,\dots,n-1\}$ presented by its Hasse diagrams $I$, every $p$-improvement $H'$ of $H$ presented by $I'$, and every allocation $X$ in the core of $H$:
--
--   1. the program `hmImproveProg I I' X p` performs at most $C\cdot|H|$ unit operations, with $|H|$ the length of the description of $H$ (not of $H'$);
--   2. the program implements HM-Improve: some run of the algorithm stops in a state $(Y,R)$ such that the program's result is the output of that state for some allocation $X_R$ in the core of $H'_{R\cap N}$.
--
--   Differences from the source:
--   - correction: a (p,q)-improvement satisfies (i) a ≺′_q b ⇔ a ≺_q b for a, b ≠ p, and (ii) a ≺_q p ⇒ a ≺′_q p (p.9) → IsImprovementAt adds clause (iii): p ≺′_q a ⇒ p ≺_q a for every a; reason: with (i) and (ii) only, Theorem 2 is false: N = {p, q, a}, p ranks q above a above p, a ranks q above a with p unacceptable, q has p and a incomparable above q in H and a above p above q in H′; the swap (p q) is in the core of H and every core allocation of H′ gives p the house of a or her own (proved in the verification file); for strict orders (iii) follows from (ii)
--   - reading: a (p,q)-improvement for agents p and q (q = p not excluded) → q ≠ p; reason: p.12 says the preferences of p remain unchanged; with q = p the theorem fails (N = {p, b}, p raises her own house above b's: the swap is in the core of H, the only core allocation of H′ gives p her own house)
--   - reading: a sequence of (p,q_i)-improvements for some k ∈ ℕ → a list of any length, k = 0 (H′ = H) included; reason: whether 0 ∈ ℕ is not fixed by the paper; for k = 0 every statement holds with X′ = X
--   - reading: Q = {q_i : X(q_i) ≺′_{q_i} p}, with q_1, …, q_k the improving agents (p.11; Algorithm 1, line 2 filters ≺_a ≠ ≺′_a) → Qset H′ X p = {a ≠ p : X(a) ≺′_a p}; reason: an agent whose preferences did not change undergoes a trivial (p, a)-improvement, so the series q_1, …, q_k may list every agent other than p; the proofs do not use the filter
--   - generalization: the iteration starts only when X is not in the core of H′ (p.11, Algorithm 1, line 1) → every run from hmInit, whether or not X is in the core of H′; reason: the proofs of §4.2 never use that X is not in the core of H′; the source's runs are among the runs covered
--   - correction: (a, b) ∈ E is Y-augmenting if a ∈ V or Y(a) ≺_a b (p.11) → (a ∈ V and b ≠ a) or Y(a) ≺_a b; reason: (a, a) ∈ E for every a, so the literal definition puts a loop at every sink and no sub-allocation with a sink is stable, which makes Lemma 1 false; its proof and Step 2 use no loop
--   - encoding: H̃ keeps the preferences of H′ (with q̃ in the place of p for q) → tildeMarket keeps them among acceptable houses; houses unacceptable to an agent are below every acceptable one and mutually incomparable; reason: the acceptability graph G̃ is exactly the page's; every statement compares acceptable houses only
--   - encoding: the algorithm HM-Improve with its free choices → every chain of HMStep transitions from hmInit (HMReachable); reason: one transition per choice the page leaves free; each run of the page is such a chain
--   - reading: |H| (not defined in Theorem 2) → HassePres.size: Σ_a (vertices + arcs of the Hasse diagram H_a); reason: Appendix A, p.30 defines |H| = Σ_a |H_a|; |H_a| counts vertices and arcs, as the bound O(|N| + Σ_a |H_a|) = O(|H|) on p.30 needs
--   - reading: O(|H|) time → one universal constant C, placed before the instance, bounding the number of unit operations of the concrete charged program; reason: unit-cost RAM; the program is a specific definition under the charging discipline of Prog, so the bound cannot be met by a cost-free Lean function
--   - encoding: given H, H′ and X (and p) → Hasse-diagram presentations I of H and I′ of H′ (vertex, out- and in-neighbour lists), X as a function, p; reason: the input format of Appendix A, p.30; Represents ties each presentation to its market
--   - reading: O(|H|) for inputs H, H′, X → the bound is C · |H| with |H| the size of I, not of I′; reason: the literal statement; |H′| can be of order |H|², and hmImproveProg reads I′ only at p
--   - encoding: an allocation is a set X ⊆ E with δ⁻_X(a) = δ⁺_X(a) = 1, and X is in the core if G^H_{X≺} is acyclic → Equiv.Perm N with every X(a) acceptable to a; the core as ¬TransGen of the X-augmenting relation at every agent; reason: same objects
-- source:
--   Schlotter, Biró, Fleiner, The core of housing markets from an agent's perspective: Is it worth sprucing up your home?, arXiv:2110.06875v3, Lemma 4, p.18

import Mathlib
import Definitions.Def_HousingImprove_IsPImprovement
import Definitions.Def_HousingImprove_Step
import Definitions.Def_HousingImprove_hmImproveProg

namespace HousingImprove

/-- **Lemma 4** (Schlotter, Biró, Fleiner, arXiv:2110.06875v3, p.18): "Algorithm HM-Improve runs in
`O(|H|)` time."

There is a universal constant `C` such that for every market `H` on `Fin n` presented by `I`, every
`p`-improvement `H'` presented by `I'`, and every allocation `X` in the core of `H`: the program
`hmImproveProg` performs at most `C · |H|` unit operations, and it implements HM-Improve: some run of
the algorithm (`HMStep` from `hmInit`, with the largest admissible `Q`, `Qset`, which the program
computes) ends in a state `s` with `U = V` such that the program's result
is the output of `s` for some allocation `X_R` in the core of `H'_{R∩N}`.

**Formalization Note.** `|H|` is `HassePres.size` of `I`, not of `I'`: `|H'|` can be of order
`|H|²`, and the bound is in `|H|` as the page states. `hmImproveProg` reads `I'` only at `p`. -/
theorem lemma_4 :
    ∃ C : ℕ, ∀ (n : ℕ) (H H' : Market (Fin n)) (I I' : HassePres n) (p : Fin n)
      (X : Equiv.Perm (Fin n)),
      Represents I H → Represents I' H' → H.IsCore X → IsPImprovement p H H' →
      ((hmImproveProg I I' X p).run 0).2 ≤ C * I.size ∧
      ∃ s : HMState (Qset H' X p), HMReachable H' X p (Qset H' X p) s ∧ s.IsTerminal ∧
        ∃ XR : Equiv.Perm s.RN, (H'.restrict s.RN).IsCore XR ∧
          s.IsOutput p XR ((hmImproveProg I I' X p).run' 0) := by sorry

end HousingImprove
