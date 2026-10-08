-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_lemma_7
-- name    : GOSNIZK.CircuitSound.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:30:34.048793+00:00
-- url     : https://prove2.me/theorems/20b7d4a9-6ac3-4b04-976b-6e6bda8b6335
-- title:
--   Lemma 7 — (K, P, V) has perfect soundness
-- statement:
--   Let a homomorphic proof commitment scheme have message space $\mathcal M=\mathbb Z/N\mathbb Z$ with $N\ge4$, and assume the homomorphic property, perfect binding and perfect soundness of the 0/1 proof. Then the Circuit SAT proof $(K,P,V)$ of Figure 3 has perfect soundness: for every $(ck,xk)$ output by $K_{\mathrm{binding}}$, every NAND circuit $C$ that has no satisfying assignment and every purported proof $\pi$,
--   $$V(ck,C,\pi)=0.$$
--
--   Soundness holds against unbounded provers, so the protocol is a proof, not only an argument, on binding keys.
--
--   **Formalization Note** The paper's $\Pr[\sigma\leftarrow K(1^k);\pi\leftarrow\mathcal A(\sigma,x_k):V(\sigma,x_k,\pi)=1]=0$ for all adversaries is stated for every key in the support of $K_{\mathrm{binding}}$ and every $\pi$. The order bound $N\ge4$ is the paper's standing choice on p. 14; for $N=3$ the protocol of Figure 3 is not sound (the all-zero assignment passes every gate check).
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, Lemma 7

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

namespace GOSNIZK.CircuitSound

/-- Lemma 7 (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive Zero-Knowledge*, J. ACM
59(3) (2012), authors' version of March 7, 2011, p. 15): the protocol of Figure 3 has perfect
soundness, for a homomorphic, perfectly binding commitment whose 0/1 proof is perfectly sound and
whose message space has order at least 4. -/
theorem lemma_7 {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hsound01 : S.PerfectSoundness01) :
    S.CircuitPerfectSoundness := by sorry

end GOSNIZK.CircuitSound
