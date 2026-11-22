-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_verifierProcedure_spec
-- name    : LinearSetReconciliation327.Main.verifierProcedure_spec
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T12:36:00.404032+00:00
-- url     : https://prove2.me/theorems/59475ec6-afe3-48ce-bc9c-fe8ed4de3287
-- title:
--   Pinsketch decoder, stage 4 (accepted statement): the verifier contract with its memory frame
-- statement:
--   **The accepted verifier-stage statement of Proposition 2.1, published verbatim.**  From a memory whose slot $79$ is the expected-array base $EB$, slot $85$ the output base $BP$, slot $86$ the verification base $V$, slot $m\,77$ the dimension $w$, slot $80$ the parameter $t$, slot $101$ the candidate count and slot $100$ the incoming flag, holding the candidate list as an output list at $BP$ and the expected array at $EB$, the compiled verifier `verifierProcedure` halts in $423$ steps; the final flag is $\mathrm{flag}\cdot\mathrm{equalPrefix}$ of the stored and recomputed power sums, the output list and the two metadata slots $85,101$ are preserved, and **every word outside `verifierWritable V (2t)` is unchanged**.  The last conjunct is what the published `pinsketch_decoder_verifier` dropped.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch, PDF p.10); the verifier stage of the Proposition 2.1 decoder.  Accepted source: `Solutions/Sol_proposition_2_1.lean:15341-15407` (`verifierProcedure_spec`).

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.verifierProcedure_spec {F : Type} [Field F] [Algebra (ZMod 2) F] [DecidableEq F] {w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (t N : ℕ) (P : Program) (E : RAMEnv)
    (pc EB BP V T flag : ℕ) (e : ℕ → F) (xs : List ℕ) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile verifierProcedure pc))
    (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι)
    (hmeta : (121 : ℕ) < 2 ^ E.W) (hN : N < 2 ^ w) (hflag : flag ≤ 1)
    (hBP : 128 ≤ BP) (hBPword : BP + T ≤ 2 ^ E.W) (hV : 128 ≤ V) (hVfit : V < 2 ^ E.W) (hVword : V + 2 * t ≤ 2 ^ E.W)
    (hEB : 128 ≤ EB) (hEBword : EB + 2 * t ≤ 2 ^ E.W)
    (hdisj : BP + T ≤ V ∨ V + 2 * t ≤ BP) (hEdisj : EB + 2 * t ≤ V ∨ V + 2 * t ≤ EB)
    (hcount : xs.length ≤ T) (hrange : ∀ i ∈ xs, i < N)
    (hout : OutputStored m BP xs) (hExpected : FieldArrayStored b m EB (2 * t) e)
    (hm79 : m 79 = EB) (hm85 : m 85 = BP) (hm86 : m 86 = V) (hm77 : m 77 = w)
    (hm80 : m 80 = t) (hm101 : m 101 = xs.length) (hm100 : m 100 = flag) :
    Sem P E pc (pc + 423) (boundaryState pc m)
      (fun k z => k ≤ (85 * (2 * t) + 117) * xs.length + 86 * (2 * t) + 140 ∧ ∃ m',
        z = boundaryState (pc + 423) m' ∧ m' 100 = flag * equalPrefix e (listPowerSums ι xs) (2 * t) ∧
        m' 100 ≤ 1 ∧ (m' 100 = 1 ↔ flag = 1 ∧ ∀ j < 2 * t, e j = listPowerSums ι xs j) ∧
        m' 85 = BP ∧ m' 101 = xs.length ∧ OutputStored m' BP xs ∧
        MemoryFrame (verifierWritable V (2 * t)) m m') := by sorry
