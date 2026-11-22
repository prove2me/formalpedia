-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_verifier_frame
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_verifier_frame
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-21T12:27:54.349833+00:00
-- url     : https://prove2.me/theorems/07ee0bad-27aa-4d5e-a91e-118069f13d2b
-- title:
--   Pinsketch decoder, stage 4 strengthened: the verifier's memory frame above the decoder scratch
-- statement:
--   **Strengthening of Proposition 2.1's verification stage with the memory frame the published interface dropped.**  Let $b$ be a basis of $\mathbb{F}$ over $\mathbb{Z}_2$, $\iota$ an injection on $\{0,\dots,N-1\}$, $y$ the stored sketch, $e$ the Frobenius expansion of its payload, and $m$ a memory that is `CandidateReady` (the candidate support is stored as an output list at `decoderOutputBase t`, the saved syndrome is stored at `decoderSavedBase t`, and the metadata slots $79,80,85,86,100,101$ carry the saved base, $t$, the output base, the verification base $V=\texttt{decoderVerifyBase }t$, the ROOTSEARCH flag and the candidate count).  Then the compiled verification stage `verificationFinalProcedure` halts in at most $(170t+117)\,t + 172t + 149$ steps with `decoderPost` — the decoding disjunct of Proposition 2.1 — **and** it changes no word outside `verifierWritable V (2t)`; equivalently, it changes no word at or above $\texttt{decoderAllocEnd } t$.  This is exactly the `MemoryFrame` conjunct of the accepted `verifierProcedure_spec`, which the published stage theorem kept out of its postcondition.
-- source:
--   arXiv:2611.11409 (Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, *Linear Set Reconciliation with O(d) Additive Redundancy*), Section 2.2 (Pinsketch, PDF p.10) and the verifier stage of the Proposition 2.1 decoder; accepted source `Solutions/Sol_proposition_2_1.lean:15341` (`verifierProcedure_spec`, whose postcondition carries the frame) composed with the `finishOutput` tail (`verificationFinalProcedure_spec`, line 17435).

import Definitions.Def_LinearSetReconciliation327_Main_DecoderLemmas

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_verifier_frame
    {F : Type} [Field F] [DecidableEq F] [Algebra (ZMod 2) F] {N t w : ℕ}
    (b : Module.Basis (Fin w) (ZMod 2) F) (ι : ℕ → F) (y : Fin (t * w) → ZMod 2) (e : ℕ → F)
    (P : Program) (E : RAMEnv) (pc : ℕ) (m : ℕ → ℕ)
    (hAt : At P pc (Stmt.compile verificationFinalProcedure pc))
    (hN : 1 ≤ N) (ht : 1 ≤ t) (hw : 1 ≤ w) (hW : E.W = 8 * w) (hdet : E.det = detStd t N b ι)
    (hEnd : decoderAllocEnd t < 2 ^ E.W) (hNw : N < 2 ^ w)
    (h0 : ∀ i < N, ι i ≠ 0) (hinj : Set.InjOn ι (Set.Iio N))
    (hodd : ∀ k : Fin t, e (2 * k.val) = payloadField b y k)
    (heven : ∀ a : ℕ, 0 < a → e (2 * a - 1) = e (a - 1) ^ 2)
    (hReady : CandidateReady b ι t N e m) :
    Sem P E pc (pc + 432) (boundaryState pc m)
      (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z ∧
        MemoryFrame (verifierWritable (decoderVerifyBase t) (2 * t)) m z.mem) := by sorry
