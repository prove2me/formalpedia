-- Prove2me | Theorems.Thm_MantriCVQ_theorem_5_5
-- name    : MantriCVQ.theorem_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:13:29.693631+00:00
-- url     : https://prove2.me/theorems/b560a3b1-07ff-49c5-82ad-148d8fa8db47
-- title:
--   Theorem 5.5 — the batched protocol
-- statement:
--   Fix an admissible gate set and a code family of degree $d$ over it. There are a verifier running Protocol 5.3, a uniform quantum honest prover and a polynomial $p$ such that, for every instance of size $n$ and height $h\le h_{\max}(n)$ stored in the oracle and every claim about a node of height $j$:
--
--   1. every true claim is accepted with probability one against the honest prover;
--   2. every false claim is accepted with probability at most $1/4$ against every prover, classical or quantum, that exchanges classical messages;
--   3. the protocol is public-coin with $2j$ messages, $j$ from each party, the prover sends fewer than $n\cdot4^j/3$ bits and the verifier fewer than $n\cdot4^j$ random bits, and the verifier makes at most $4^j$ leaf queries and runs in time $4^j\,\mathrm{poly}(n,j)$;
--   4. the honest prover makes $4^j-3^j$ leaf queries and runs in time $4^j\,\mathrm{poly}(n,j)$.
--
--   With $j=h_{\max}(n)$ this gives the proof system of Theorem 1.1.
--
--   Differences from the source:
--   - reading: the honest prover runs the algorithm of Theorem 5.1 up to the decoder and measures → there exists a uniform memoryless quantum prover with properties (i) and (iv); reason: the algorithm of Theorem 5.1 is itself given only by its existence, so the prover's identity is method, not statement
--   - reading: the honest prover is a uniform quantum algorithm with the public parameters → its circuits are generated from the input string, the slot and the encoded length; reason: the parameters are public (§5.2); a circuit keyed by the input length alone cannot have the exact query count of (iv)
--   - encoding: the verifier and its resources → a PCVerifier implementing Protocol 5.3 on an encoding of (n, h, j, w, b); its time and queries are those of its machine D; reason: this makes (iii) a statement about a machine
--   - encoding: messages of the wrong format are rejected → strategies are typed by the prescribed length; reason: the event cannot occur
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 5.5, p. 22 (PDF p. 24)

import Mathlib
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_Implements53
import Definitions.Def_MantriCVQ_QProver
import Definitions.Def_MantriCVQ_acceptProb
import Definitions.Def_MantriCVQ_nodeVal
import Definitions.Def_MantriCVQ_queryCount

open QAlgorithms.Complexity QAdvFew.PoQOracle

namespace MantriCVQ

/-- **Theorem 5.5** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Theorem 5.5, p. 22 (PDF p. 24)): on a claim about a node of height `j` of an instance of size
`n`, Protocol 5.3 has the following properties. (i) It accepts every true claim with probability one when the prover is
honest. (ii) For every false claim and every prover it accepts with probability at most `1/4`. (iii) It is public-coin
with `2j` messages, `j` from each party; the prover sends fewer than `n · 4^j/3` bits and the verifier fewer than `n · 4^j`
random bits; the verifier makes at most `4^j` leaf queries and runs in time `4^j poly(n, j)`. (iv) The honest prover makes
`4^j - 3^j` leaf queries and runs in time `4^j poly(n, j)`.

**Formalization Note** The protocol is the `PCVerifier` of `Implements53`, whose schedule gives the `2j` slots, prover
first. The honest prover is stated existentially, as a uniform memoryless `QProver`; the paper's prover has this form.
Its queries and size are summed over its `j` slots along a transcript of the schedule. The verifier's time is the step
count of its machine `D`, whose queries are counted by `queryCount`. -/
theorem theorem_5_5 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d) :
    ∃ (V : PCVerifier) (P : QProver G) (p : Polynomial ℕ),
      Implements53 C.code V ∧ P.Uniform ∧ P.PolyBounded ∧
      ∀ (n h j : ℕ) (w : Addr (dimsRange n j (h - j))) (b : Bool) (O : Oracle),
        1 ≤ n → j ≤ h → h ≤ hmax n →
        Valid C.code (dimsRange n 0 h) (leafTable O n) [] →
        (nodeVal C.code (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w) = b →
          acceptProb O V (P.toStrategy O) (claimInput n h j (Addr.toStr _ w) b) = 1) ∧
        (nodeVal C.code (dimsRange n 0 j) (leafTable O n) (Addr.toStr _ w) ≠ b →
          ∀ σ : Strategy, acceptProb O V σ (claimInput n h j (Addr.toStr _ w) b) ≤ 1 / 4) ∧
        (((∑ i ∈ Finset.range j, V.len (claimInput n h j (Addr.toStr _ w) b) (2 * i) : ℕ) : ℝ) <
          (n : ℝ) * 4 ^ j / 3) ∧
        (((∑ i ∈ Finset.range j, V.len (claimInput n h j (Addr.toStr _ w) b) (2 * i + 1) : ℕ) : ℝ) <
          (n : ℝ) * 4 ^ j) ∧
        ∀ tr : List Str, Conforms V (claimInput n h j (Addr.toStr _ w) b) tr →
          (V.D.result O (tup (claimInput n h j (Addr.toStr _ w) b :: tr))
              (4 ^ j * p.eval (n + j))).isSome ∧
          queryCount V.D O (tup (claimInput n h j (Addr.toStr _ w) b :: tr))
              (4 ^ j * p.eval (n + j)) ≤ 4 ^ j ∧
          (∑ i ∈ Finset.range j,
              (P.circ (claimInput n h j (Addr.toStr _ w) b) (2 * i)
                (tup (claimInput n h j (Addr.toStr _ w) b :: tr.take (2 * i))).length).queries) =
            4 ^ j - 3 ^ j ∧
          (∑ i ∈ Finset.range j,
              (P.circ (claimInput n h j (Addr.toStr _ w) b) (2 * i)
                (tup (claimInput n h j (Addr.toStr _ w) b :: tr.take (2 * i))).length).size) ≤
            4 ^ j * p.eval (n + j) := by sorry

end MantriCVQ
