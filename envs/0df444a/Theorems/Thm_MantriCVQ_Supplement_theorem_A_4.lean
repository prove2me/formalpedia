-- Prove2me | Theorems.Thm_MantriCVQ_Supplement_theorem_A_4
-- name    : MantriCVQ.Supplement.theorem_A_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:11:16.984534+00:00
-- url     : https://prove2.me/theorems/639d3d79-691c-4388-824b-e2e08a7d3f58
-- title:
--   Theorem A.4 — public-coin verification with noisy code tables: completeness $0.99$, soundness $0.01$, $(2t_\eta)^j$ verifier queries
-- statement:
--   Fix a code family of Definition 3.1 and a noise rate $0\le\eta<1/4$. There is a classical public-coin interactive proof system for claims about nodes of trees that are valid with noise rate $\eta$, with completeness at least $0.99$, soundness error at most $0.01$, and a uniform quantum honest prover. There is a constant $t_\eta$ with the following bounds for a claim about a node of height $j$:
--
--   1. the verifier makes at most $(2t_\eta)^j$ leaf queries and runs in time $(2t_\eta)^j\,\mathrm{poly}(n,j)$;
--   2. the parties exchange at most $(2t_\eta)^j\,\mathrm{poly}(n,j)$ bits;
--   3. the honest prover runs in time $(2t_\eta C_\eta)^j\,\mathrm{poly}(n,j)$, where $C_\eta$ is the constant of Theorem A.3, enlarged if necessary.
--
--   A claim $(w,b)$ states that the node at address $w$ has value $b$. This protocol is the verification part of Theorem 7.4, run on the claim that the root has value one.
--
--   **Formalization Note** The claim is the base mission's input `claimInput n h j w b` for a node of height $j$ in an instance of size $n$ and height $h$; the hypothesis is that the subtree at $w$ is valid with noise rate $\eta$. Bits exchanged are all slot lengths of the schedule; verifier queries and time are those of its decision machine along every transcript of the schedule; prover time is the total circuit size at its slots.
--
--   Differences from the source:
--   - generalization: claims about nodes of trees that are valid with noise rate η → claims about the node at w whenever the subtree at w is valid with noise rate η (the rest of the instance arbitrary); reason: a node of a valid tree has a valid subtree, so this covers every claim of the paper
--   - generalization: soundness against computationally unbounded provers, classical or quantum, that communicate classically → soundness against every map from input and transcript to a distribution on the next message; reason: every such prover induces these conditional laws, so the class of strategies contains all of them
--   - encoding: verifier ≤ (2t)^j leaf queries and time (2t)^j poly(n, j); at most (2t)^j poly(n, j) bits; honest prover time (2t C_η)^j poly(n, j) → along every transcript of the schedule the decision machine halts within (2t)^j p(n + j) steps with ≤ (2t)^j queries; the sum of all slot lengths ≤ (2t)^j p(n + j); the prover's circuit sizes at its slots sum to ≤ (2t C)^j p(n + j); reason: the base mission's Theorem 5.5 conventions for queries, time and bits
--   - reading: a constant t_η; C_η the constant of Theorem A.3, enlarged if necessary → ∃ t > 0 and ∃ C (natural numbers) after η and the code family, then one polynomial p; reason: an enlarged constant only weakens the bound, so the content is that some C works
--   - reading: a uniform quantum honest prover → a memoryless uniform polynomial-size QProver over G, one circuit per slot, measured; reason: a special case, so its existence is stronger (as in the base mission)
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem A.4, p. 45 (PDF p. 47); protocol and proof pp. 45–47 (PDF pp. 47–49)

import Mathlib
import Definitions.Def_MantriCVQ_Supplement_nodeValNoisy
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_leafTable
import Definitions.Def_MantriCVQ_Implements53
import Definitions.Def_MantriCVQ_QProver
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_queryCount

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ.Supplement

open MantriCVQ

/-- **Theorem A.4** (Public-coin verification with noisy code tables; Mantri, arXiv:2610.37635 (PDF
sha256 d1fab777…1d0b33), Theorem A.4, p. 45 (PDF p. 47)): for every fixed `0 ≤ η < 1/4` there is a
classical public-coin interactive proof system for claims about nodes of trees that are valid with
noise rate `η`, with completeness at least `0.99`, soundness error at most `0.01`, and a uniform
quantum honest prover. There is a constant `t_η` with the following bounds for a claim about a node of
height `j`: the verifier makes at most `(2t_η)^j` leaf queries and runs in time `(2t_η)^j poly(n, j)`,
the parties exchange at most `(2t_η)^j poly(n, j)` bits, and the honest prover runs in time
`(2t_η C_η)^j poly(n, j)`, where `C_η` is the constant of Theorem A.3, enlarged if necessary.

**Formalization Note** The claim `(w, b)` about the node at `w` (height `j`, instance of size `n` and
height `h`) is the input `claimInput n h j w b` of the base mission; the hypothesis is that the subtree
at `w` is valid with noise rate `η`. A true claim is accepted with probability at least `0.99` with
the honest prover, a false one with probability at most `0.01` against every strategy. The bits
exchanged are the sum of all slot lengths of the schedule; the verifier's queries and time are those
of its decision machine `D` with the oracle `O` along every transcript of the schedule; the honest
prover's time is the total size of its circuits at its slots. `t_η` is a positive integer and `C_η` a
natural number (the theorem allows `C_η` to be enlarged, so it is existential here), both chosen after
`η` and the code family, and `poly(n, j)` is one polynomial in `n + j` chosen after them. -/
theorem theorem_A_4 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d)
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η < 1 / 4) :
    ∃ (V : PCVerifier) (P : QProver G) (t Cη : ℕ) (p : Polynomial ℕ),
      0 < t ∧ P.Uniform ∧ P.PolyBounded ∧
      ∀ (n h j : ℕ) (w : Addr (dimsRange n j (h - j))) (b : Bool) (O : Oracle),
        1 ≤ n → j ≤ h → h ≤ hmax n →
        ValidNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w) →
        (nodeValNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w) = b →
          (99 : ℝ) / 100 ≤ acceptProb O V (P.toStrategy O) (claimInput n h j (Addr.toStr _ w) b)) ∧
        (nodeValNoisy C.code η (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w) ≠ b →
          ∀ σ : Strategy, acceptProb O V σ (claimInput n h j (Addr.toStr _ w) b) ≤ 1 / 100) ∧
        (∑ i ∈ Finset.range (V.S (claimInput n h j (Addr.toStr _ w) b)),
            V.len (claimInput n h j (Addr.toStr _ w) b) i) ≤ (2 * t) ^ j * p.eval (n + j) ∧
        ∀ tr : List Str, Conforms V (claimInput n h j (Addr.toStr _ w) b) tr →
          (V.D.result O (tup (claimInput n h j (Addr.toStr _ w) b :: tr))
              ((2 * t) ^ j * p.eval (n + j))).isSome ∧
          queryCount V.D O (tup (claimInput n h j (Addr.toStr _ w) b :: tr))
              ((2 * t) ^ j * p.eval (n + j)) ≤ (2 * t) ^ j ∧
          (∑ i ∈ (Finset.range (V.S (claimInput n h j (Addr.toStr _ w) b))).filter
                (fun i => V.proverSlot (claimInput n h j (Addr.toStr _ w) b) i = true),
              (P.circ (claimInput n h j (Addr.toStr _ w) b) i
                (tup (claimInput n h j (Addr.toStr _ w) b :: tr.take i)).length).size) ≤
            (2 * t * Cη) ^ j * p.eval (n + j) := by sorry

end MantriCVQ.Supplement
