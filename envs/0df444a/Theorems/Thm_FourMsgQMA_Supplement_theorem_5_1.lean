-- Prove2me | Theorems.Thm_FourMsgQMA_Supplement_theorem_5_1
-- name    : FourMsgQMA.Supplement.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T16:33:41.720382+00:00
-- url     : https://prove2.me/theorems/b831c505-fbbb-4e70-92f2-6de16e1c1cf8
-- title:
--   Theorem 5.1 — negligible circuit-policy soundness
-- statement:
--   This is Theorem 5.1 (negligible circuit-policy soundness) in the pinned-down version requested by the operator.
--
--   Let $L$ be a QMA promise problem with verification family $F$. Assume:
--
--   1. negligible base soundness (Definition 3.7) at every admissible resource bound;
--   2. uniform correctness and IND-CPA security of the FHE (Definitions 3.14, 3.15);
--   3. index hiding and statistical extraction consistency of the block commitment $\mathrm{SC}$ (Definitions 3.17, 3.18);
--   4. both halves of Definition 3.22 (index hiding and semi-adaptive extraction) for the index BARG $\mathrm{IB}$;
--   5. binding of local openings (Definition 3.13) of the Merkle commitments, and collapsing (Definition 3.12) of the bit-vector Merkle commitment used for the selection;
--   6. guaranteed extraction (Definition 3.25) of Kilian's argument for the authorization relation $R_{\mathrm{auth}}$.
--
--   Then for every valid choice of the circuits and bounds the construction leaves open, and whatever its honest-prover component, the four-message construction of §5.1 satisfies **selective circuit batch soundness** (Definition 3.6) with negligible error: for every fixed sequence of polynomial-size policies and no-batches $(C,X)$ and every QPT prover with quantum advice, the acceptance probability is negligible.
--
--   This is the soundness half of Corollary 5.15.
--
--   Differences from the source:
--   - reading: "index-BARG index hiding and extraction in Definitions 3.22 and 3.22" → IndexBARG.Secure, the two halves of Definition 3.22 (index hiding and semi-adaptive extraction); reason: the repeated label is a typo; Definition 3.22 states both properties (p.21)
--   - reading: "negligible base soundness in Definition 3.7" → baseSoundAt: negligible acceptance for every polynomially bounded resource bound T(λ) ≥ t_L(x_λ); reason: §5.1 runs one Gen(1^λ, T) with T bounding all local resources (p.34)
--   - reading: "extraction consistency in Definition 3.18" → SEC.StatExtractConsistent (the statistical form); reason: "We use the stronger statistical property" (p.19)
--   - reading: "Merkle binding in Definition 3.13; collapsing of the selection commitment in Definition 3.12" → MerkleBinding P.mt for the balanced tree of the hash family P.mt, and Collapsing of the bit-vector commitment x ↦ MerkleRoot(x) with the whole vector as preimage register; reason: §3.8 (p.16): "collapsing of the vector commitment means Definition 3.12 for the map x ↦ Commit(hk, x)"
--   - reading: "Kilian guaranteed extraction in Definition 3.25" → P.kil.GuaranteedExtraction for R_auth (Figure 4) with the declared bounds I.authIn, I.authWit; reason: the authorization proof is the only Kilian proof of §5.1 (p.34)
--   - reading: "the four-message construction" → circuitPolicyArg P I F hon for every implementation choice I with I.Valid and every honest-prover component hon; reason: the paper leaves the circuits for V, G, the constant one and C_θ and the bounds L, B_C, m_C and the fixed format bound aLen on α_µ (checked by Dec, since "The final decision checks the fixed formats", p.37) implicit; I.Valid asks for C_θ only at the θ the verifier can form and for depth ≤ L only on the inputs each circuit is evaluated on; soundness does not depend on the honest prover; the stronger reading
--   - encoding: Definition 3.6 with error negl(λ), local resource bound T → the published Arg4.SelectivelySound; T = t(X) = max_i t_L(x_i); reason: base mission's Arg4 and its decision 6 (t(X) in place of T)
--   - encoding: [k] = {1, …, k}, fields of M1–M4, encrypted secrets → 1-based indices with Merkle positions i − 1; each message the pack of its fields; secret keys and the base tape encrypted bit by bit; verifier coin lengths the least bounds covering every instance of the given size; reason: Lean representation
-- source:
--   Goyal, Koppula, Four-Message Arguments for NP ∘ batchQMA and Six-Message Arguments for QMA from LWE, STOC 2027 submission (sha256 6c523d45…), Theorem 5.1, p.38 (PDF 40); §5.1, pp.33–38 (PDF 35–40)

import Mathlib
import Definitions.Def_FourMsgQMA_Arg4_SelectivelySound
import Definitions.Def_FourMsgQMA_Supplement_CircuitPolicyArg
import Definitions.Def_FourMsgQMA_Supplement_GuaranteedExtraction

namespace FourMsgQMA

namespace Supplement

open QAlgorithms.Complexity TightPQRepetition.Main

/-- **Theorem 5.1** (Negligible circuit-policy soundness), Goyal, Koppula, STOC 2027 submission
(sha256 6c523d45…), p.38 (PDF 40): "Assume negligible base soundness in Definition 3.7; FHE
correctness and CPA security in Definitions 3.14 and 3.15; commitment index hiding and extraction
consistency in Definitions 3.17 and 3.18; index-BARG index hiding and extraction in Definitions 3.22
and 3.22; Merkle binding in Definition 3.13; collapsing of the selection commitment in Definition
3.12; and Kilian guaranteed extraction in Definition 3.25. Then the four-message construction
satisfies the selective circuit soundness game of Definition 3.6 with error negl(λ)."

Let `L` be a QMA promise problem with verification family `F`. For primitives with negligible base
soundness at every admissible resource bound (Definition 3.7), uniformly correct and IND-CPA-secure
FHE (Definitions 3.14, 3.15), an index-hiding and statistically extraction-consistent block
commitment (Definitions 3.17, 3.18), an index BARG satisfying both halves of Definition 3.22, a
Merkle commitment with binding local openings (Definition 3.13) whose bit-vector commitment is
collapsing (Definition 3.12), and Kilian's argument with guaranteed extraction for the
authorization relation `R_auth` (Definition 3.25), and for every valid choice of the circuits and
bounds the construction leaves open, the four-message construction of §5.1 satisfies negligible
selective circuit batch soundness (Definition 3.6), whatever its honest-prover fields.

**Formalization Note** "Definitions 3.22 and 3.22" is read as the two halves of Definition 3.22
(`IndexBARG.Secure`). The extraction consistency is the statistical form the paper uses (p.19). -/
theorem theorem_5_1 (L : PromiseProblem) (F : QMAFamily) (hLF : IsQMAVerifierFor L F)
    (P : CPPrims) (I : CPImpl)
    (hbase : baseSoundAt P.base L F) (hcor : P.fhe.UniformlyCorrect) (hcpa : P.fhe.INDCPA)
    (hhid : P.sc.IndexHiding) (hext : P.sc.StatExtractConsistent) (hib : P.ib.Secure)
    (hbind : MerkleBinding P.mt) (hcol : (merkleBitHash P.mt).Collapsing)
    (hge : P.kil.GuaranteedExtraction (rauth P.mt I.authIn I.authWit)) (hI : I.Valid P F)
    (hon : (ℕ → ℕ → ℕ) × (ℕ → Bits → Bits → Core) × (ℕ → Bits → Bits → ℕ → Bits → Bits) ×
      (ℕ → Bits → Bits → ℕ → Bits → Bits)) :
    (circuitPolicyArg P I F hon).SelectivelySound L := by sorry

end Supplement

end FourMsgQMA
