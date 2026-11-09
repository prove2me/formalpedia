-- Prove2me | Theorems.Thm_KColoringFaster_ListBootstrap_corollary_3_8
-- name    : KColoringFaster.ListBootstrap.corollary_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:51.167+00:00
-- url     : https://prove2.me/theorems/e5221e1d-e1b4-49cb-8a6e-7a8b0e20161c
-- title:
--   Corollary 3.8 — two-block list-coloring
-- statement:
--   Consider a list-coloring instance $(G,L)$ on $n$ vertices with colors in $\mathbb N$, together with a set $Q$ of colors; write $R$ for the colors outside $Q$, so the palette is $P=Q\,\dot\cup\,R$. Let
--   $$A=\{v: L(v)\subseteq Q\},\qquad B=\{v: L(v)\subseteq R\}.$$
--   Then a single algorithm, given $(G,L)$ and $Q$, decides list colorability in
--   $$O^*\big(2^{n-|A|}+2^{n-|B|}\big)$$
--   time, with one-sided error at most $e^{-n}$. Since $A$ and $B$ are the largest sets with $L(v)\subseteq Q$ on $A$ and $L(v)\subseteq R$ on $B$, the same bound holds for every such pair of sets. In particular, for every real $\eta$, on every input with $|A|,|B|\ge\eta n$ the same algorithm runs in $O^*(2^{(1-\eta)n})$ time on every coin string.
--
--   This is the terminal step of Theorem 5.1: there, $A$ is a set of restricted star leaves and $B$ a set of star centers.
--
--   **Formalization Note** Algorithms and $O^*$ are as in `Algorithms`; the input is encoded as in `TwoBlock`. The "in particular" clause is stated with the same program and the same polynomial as the main bound.
--
--   Differences from the source:
--   - reading: "Suppose that $A,B$ satisfy …" for given sets $A,B$ → the bound with the largest such sets $A=\{v:L(v)\subseteq Q\}$, $B=\{v:L(v)\subseteq R\}$; reason: every admissible pair is contained in these and the bound is monotone, so this is the source's claim for all admissible $A,B$ at once
--   - reading: $P=Q\,\dot\cup\,R$ → the algorithm receives $Q$, and $R$ is the set of colors outside $Q$; reason: the partition is part of the input in the source's use (Algorithm 3, p. 26, "TwoBlockListColoring(I′; Q, R)"); colors outside all lists play no role
--   - reading: "can be decided" → decided with one-sided error at most $e^{-n}$; reason: §3 (p. 7) allows exponentially small error for all algorithms and says errors can be taken one-sided
--   - encoding: "and exponential space" → space not bounded separately; reason: a run of cost $B$ touches at most $B$ memory cells
--   - encoding: $O^*(\cdot)$ time → one program and polynomials $p,q$ fixed before the input, worst-case cost $\lceil p(\sigma)\,T\rceil$ on the integer RAM with registers of at most $q(\sigma)$ bits; reason: unit cost with polynomially bounded registers equals bit cost up to polynomial factors
--   - generalization: nonempty lists → lists may be empty; reason: the proof rejects an empty list immediately (p. 11), and the source's instances are included
-- source:
--   Zamir, k-Coloring is Faster than Computing the Chromatic Number, arXiv:2607.25973 (revision of 9 Sep 2026; STOC 2027 submission #73; source.pdf sha256 624fee950171ffcd169c0aa08efcb25b2de77b3219fcbdf9227d838138d1003e), p. 11, Corollary 3.8

import Mathlib
import Definitions.Def_KColoringFaster_ListBootstrap_Instances
import Definitions.Def_KColoringFaster_ListBootstrap_Algorithms
import Definitions.Def_KColoringFaster_ListBootstrap_TwoBlock

open Classical

namespace KColoringFaster.ListBootstrap

open CongruencyTU

/-- Corollary 3.8 (Two-block list-coloring), p. 11. Given a list instance on `n` vertices and a block
`Q` of the palette (`R` the colors outside `Q`), list colorability is decided by one program in
`O*(2^{n-|A|} + 2^{n-|B|})` time with one-sided error at most `e^{-n}`, where `A = {v : L(v) ⊆ Q}` and
`B = {v : L(v) ⊆ R}` are the largest sets with the corollary's property (so the bound holds for every
admissible `A, B`). In particular, the same program, on inputs with `|A|, |B| ≥ η n`, runs in
`O*(2^{(1-η) n})` time on every coin string. -/
theorem corollary_3_8 :
    ∃ (P : Program) (p q : Polynomial ℕ),
      RandDecidesBy P p q encListQ (fun J => J.I.n) (fun _ => True) (fun J => ListColorable J.I)
        (fun J => (2 : ℝ) ^ (J.I.n - J.supportedQ.card) + (2 : ℝ) ^ (J.I.n - J.supportedR.card))
        (expErr 1) zeroErr ∧
      ∀ (η : ℝ) (J : ListQInstance),
        η * J.I.n ≤ J.supportedQ.card → η * J.I.n ≤ J.supportedR.card →
          ∀ c : Fin (budget p (encListQ J)
              ((2 : ℝ) ^ (J.I.n - J.supportedQ.card) + (2 : ℝ) ^ (J.I.n - J.supportedR.card))) →
              Bool,
            RunBounded P noOracle (extendCoins c) (encListQ J)
              (budget p (encListQ J) ((2 : ℝ) ^ ((1 - η) * J.I.n))) q 0 := by sorry

end KColoringFaster.ListBootstrap
