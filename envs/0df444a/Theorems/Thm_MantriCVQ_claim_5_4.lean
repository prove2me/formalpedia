-- Prove2me | Theorems.Thm_MantriCVQ_claim_5_4
-- name    : MantriCVQ.claim_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:12:41.532129+00:00
-- url     : https://prove2.me/theorems/25696add-e3ec-4081-bf2a-7bb4732f6efe
-- title:
--   Claim 5.4 — joint soundness for lists of claims
-- statement:
--   Fix a valid tree and $j\ge0$. Consider any list of claims about nodes of height $j$ on which $F$ claims are false, any prover, classical or quantum, that exchanges classical messages with the verifier, and any history of the interaction before the list is processed. Then, conditioned on this history, Protocol 5.3 continued from this list accepts with probability at most $4^{-F}$. The bound depends only on the number of false claims and holds at every height, and this is why three code checks per entry are needed.
--
--   Differences from the source:
--   - encoding: conditioned on any history, any prover → every history string list and every continuation strategy; reason: the conditional behaviour of any prover after a fixed history is again a strategy
--   - encoding: messages of the wrong format are rejected → strategies are typed by the prescribed length; reason: the event cannot occur
-- source:
--   Mantri, Classical Verification of Quantum Computation Beyond the Polynomial Hierarchy, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 5.4, p. 21 (PDF p. 23)

import Mathlib
import Definitions.Def_MantriCVQ_Addr
import Definitions.Def_MantriCVQ_Admissible
import Definitions.Def_MantriCVQ_CodeFamily
import Definitions.Def_MantriCVQ_Protocol53
import Definitions.Def_MantriCVQ_dimsRange
import Definitions.Def_MantriCVQ_nodeVal

open QAlgorithms.Complexity

namespace MantriCVQ

/-- **Claim 5.4** (Mantri, arXiv:2610.37635 (PDF sha256 d1fab777…1d0b33), Claim 5.4, p. 21 (PDF p. 23)): fix a valid tree and `j ≥ 0`. For any list of claims about nodes
of height `j` on which `F` claims are false, any prover and any history before the list is processed, Protocol 5.3
continued from this list accepts with probability at most `4^{-F}`.

**Formalization Note** "Conditioned on any history" is "for every history `hist` and every continuation strategy `σ`":
the conditional behaviour of any prover after a fixed history is again a strategy. False claims are counted with
repetition (entries of the list). -/
theorem claim_5_4 {G : List Gate} (hG : Admissible G) {d : ℕ} (C : CodeFamily G d)
    {n h j : ℕ} (hn : 1 ≤ n) (hj : j ≤ h) (hh : h ≤ hmax n) (Y : Str → Bool)
    (hY : Valid C.code (dimsRange n 0 h) Y [])
    (L : List (Str × Bool))
    (hL : ∀ e ∈ L, ∃ a : Addr (dimsRange n j (h - j)), e.1 = Addr.toStr _ a)
    (σ : Strategy) (w : Str) (hist : List Str) :
    accept53 C.code Y σ w (dimsRange n 0 j) hist L ≤
      ((4 : ℝ) ^ (L.countP fun e => nodeVal C.code (dimsRange n 0 j) Y e.1 != e.2))⁻¹ := by sorry

end MantriCVQ
