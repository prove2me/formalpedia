-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_verifier
-- name    : LinearSetReconciliation327.Main.pinsketch_decoder_verifier
-- status  : Proved
-- author  : @djwj233
-- created : 2026-11-19T12:42:35.344266+00:00
-- url     : https://prove2.me/theorems/9aef1da9-1951-43c0-a5eb-0bcac74478c3
-- title:
--   Pinsketch decoder, stage 4: verification of the candidate support
-- statement:
--   This is the contract of the fourth stage of the Pinsketch decoder: the verifier.
--
--   Given a state satisfying `CandidateReady`, together with the field facts that the evaluation point is injective and nonzero on $\{0,\dots,N-1\}$ and that the stored entries encode the payload and its Frobenius squares ($e_{2k} = \operatorname{payloadField}_b(y)_k$ and $e_{2a-1} = e_{a-1}^{2}$), the verifier executes `verificationFinalProcedure` from program counter `pc` and halts within $432$ steps. The resulting state satisfies `decoderPost`: the accept/reject flag is nonzero exactly when a vector of Hamming weight at most $t$ has the given syndrome, and in the accepting case the output region holds that vector's support.
--
--   Thus the verifier is both sound and complete for the decoding relation: it accepts precisely the light vectors with the stored sketch, and rejects only when none exists. The check is the cardinality/legal-position test followed by a comparison of the reconstructed power sums.
--
--   **Formalization Note** The step bound $(170t+117)t + 172t + 149$ counts the $O(t^{2})$ legal-position scan and the $O(t)$ power-sum comparison.
-- source:
--   arXiv:2611.11409, Section 2.2 (Pinsketch decoder, verification stage) and Appendix C; Dodis, Ostrovsky, Reyzin, Smith, Fuzzy Extractors: How to Generate Strong Keys from Biometrics and Other Noisy Data, SIAM J. Comput. 38(1), 2008, Section 6.3

import Definitions.Def_LinearSetReconciliation327_Main_Basic
import Definitions.Def_LinearSetReconciliation327_Main_Pinsketch
import Definitions.Def_LinearSetReconciliation327_Main_DecoderModel
import Definitions.Def_LinearSetReconciliation327_Main_DecoderTables
import Definitions.Def_LinearSetReconciliation327_Main_DecoderProgram
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_syndrome_recovery
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_read
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_key_solver
import Theorems.Thm_LinearSetReconciliation327_Main_pinsketch_decoder_root_search

set_option autoImplicit false

open Finset

theorem LinearSetReconciliation327.Main.pinsketch_decoder_verifier
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
      (fun k z => k ≤ (170 * t + 117) * t + 172 * t + 149 ∧ decoderPost (N := N) b ι y z) := by sorry
