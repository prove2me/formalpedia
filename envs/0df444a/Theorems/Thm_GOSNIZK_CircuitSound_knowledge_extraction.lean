-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_knowledge_extraction
-- name    : GOSNIZK.CircuitSound.knowledge_extraction
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:48.361987+00:00
-- url     : https://prove2.me/theorems/943df98a-48c3-471e-b7d8-bd68d6ea4610
-- title:
--   Proof of Theorem 6 — with perfect extractability, the wire values extracted from an accepted proof satisfy the circuit
-- statement:
--   Let a homomorphic proof commitment scheme have message space $\mathcal M=\mathbb Z/N\mathbb Z$ with $N\ge4$, and assume the homomorphic property, perfect binding, perfect soundness of the 0/1 proof and perfect extractability. Let $E_1=K_{\mathrm{binding}}$ and let $E_2(\sigma,xk,C,\pi)$ set $w_i=1$ iff $\mathrm{Ext}_{xk}(c_i)=1$. Then for every $(ck,xk)$ output by $K_{\mathrm{binding}}$, every NAND circuit $C$ and every proof $\pi$ with $V(ck,C,\pi)=1$,
--   $$C\big(E_2(ck,xk,C,\pi)\big)=1.$$
--
--   So the protocol of Figure 3 is a perfect proof of knowledge.
--
--   **Formalization Note** The extractor is fixed to the one in the paper's proof; an unspecified extractor would make the claim follow from soundness by exhaustive search, which is not what the paper proves.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, proof of Theorem 6 (second paragraph)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

namespace GOSNIZK.CircuitSound

/-- Perfect knowledge extraction (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive
Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, proof of Theorem 6, p. 15):
if the commitment scheme is perfectly extractable, the wire values extracted from the commitments of
an accepted proof satisfy the circuit, on every binding key. -/
theorem knowledge_extraction {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) (hext : S.PerfectExtractability) :
    S.CircuitPerfectKnowledgeExtraction := by sorry

end GOSNIZK.CircuitSound
