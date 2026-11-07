-- Prove2me | Theorems.Thm_MinBisectFPT_lemma_3_1
-- name    : MinBisectFPT.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:56:23.705595+00:00
-- url     : https://prove2.me/theorems/ba493b0d-689a-4b21-ab2b-130eb118f34e
-- title:
--   Lemma 3.1 — important cuts: existence, at most $4^p$, listing (corrected: $p+1$)
-- statement:
--   Let $H$ be a graph and $A_0,B_0\subseteq V(H)$ disjoint and nonempty.
--
--   1. For every $(A_0,B_0)$-cut $F$ there is an important $(A_0,B_0)$-cut $F'$ with $|F'|\le|F|$ and $R_H(F)\subseteq R_H(F')$.
--   2. For every $p\ge0$ there are at most $4^p$ important $(A_0,B_0)$-cuts of size at most $p$.
--   3. They can be listed in time $O(4^p(p+1)(|V(H)|+|E(H)|))$: there is a program and a constant $C$ such that, for every instance and every word size $W$ with $(|V(H)|+|E(H)|+p+2)^C\le2^W$, the program writes a duplicate-free list of exactly these cuts within $C\,4^p(p+1)(|V(H)|+|E(H)|)$ steps.
--
--   This lemma is the source of the single-exponential bounds of the paper: it lists the candidates of the dynamic program and the reachable sets of the decomposition.
--
--   Differences from the source:
--   - correction: $O(4^pp(|V(H)|+|E(H)|))$ → `C * 4^p * (p+1) * (n + edgeCount H)`; reason: at $p=0$ the printed bound is $0$, while $p\ge0$ is printed explicitly and every run on every instance takes at least one step; for $p\ge1$ the two differ by a factor at most $2$
--   - reading: an unspecified machine with a time linear in the graph size → the published unit-cost word RAM on preloaded memory, program and constant before the instance, with the word bound `(n + edgeCount H + p + 2)^C ≤ 2^W`; reason: the printed time cannot hold on a Turing machine, which needs more than linear time to read a graph; this is the standard word size
--   - encoding: $H$ a graph → `SimpleGraph (Fin n)`; reason: every finite graph is isomorphic to one
-- source:
--   Anand, Kipouridis, Węgrzycki, Counting over Unbreakable Decompositions, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 3.1, p.9

import Mathlib
import Definitions.Def_FixedMachinePrec_RAM
import Definitions.Def_MinBisectFPT_IsImportant
import Definitions.Def_MinBisectFPT_encodeCuts

open scoped Classical

namespace MinBisectFPT

/-- **Lemma 3.1 (important cuts).** Anand, Kipouridis, Węgrzycki, STOC 2027 submission (manuscript sha256 8db80a52…), Lemma 3.1, p.9. Clause (i); the count in clause (ii); and the
listing of clause (ii) on the published unit-cost word RAM.

**Formalization Note** The program `P` and the constant `C` come before the instance. The memory is
preloaded and the word size is polynomial in the instance's numbers, since the printed time is linear in
`|V| + |E|`. The printed bound `O(4^p p (|V| + |E|))` is `0` at `p = 0`, where a program still spends
a step, so `p + 1` replaces `p`. -/
theorem lemma_3_1 :
    (∀ (n : ℕ) (H : SimpleGraph (Fin n)) (A0 B0 : Finset (Fin n)),
      A0.Nonempty → B0.Nonempty → Disjoint A0 B0 →
        (∀ F, IsCut H A0 B0 F →
          ∃ F', IsImportant H A0 B0 F' ∧ F'.card ≤ F.card ∧ reach H A0 F ⊆ reach H A0 F') ∧
        ∀ p : ℕ, (Finset.univ.filter fun F : Finset (Sym2 (Fin n)) =>
          IsImportant H A0 B0 F ∧ F.card ≤ p).card ≤ 4 ^ p) ∧
    ∃ (P : List FixedMachinePrec.RAMInstr) (C : ℕ),
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)) (A0 B0 : Finset (Fin n)) (p W : ℕ),
        A0.Nonempty → B0.Nonempty → Disjoint A0 B0 →
        (n + edgeCount H + p + 2) ^ C ≤ 2 ^ W →
        ∃ L : List (Finset (Sym2 (Fin n))), L.Nodup ∧
          (∀ F, F ∈ L ↔ IsImportant H A0 B0 F ∧ F.card ≤ p) ∧ L.length ≤ 4 ^ p ∧
          ∃ b, FixedMachinePrec.ramExec (W := W) P (C * 4 ^ p * (p + 1) * (n + edgeCount H)) 0
            (cutsMem W H A0 B0 p) [] [] = some (b, encodeCuts L) := by sorry

end MinBisectFPT
