-- Prove2me | Theorems.Thm_GOSNIZK_CircuitSound_theorem_6
-- name    : GOSNIZK.CircuitSound.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:25.922865+00:00
-- url     : https://prove2.me/theorems/41367cc5-27c2-4d1a-b9a8-859792ee30a7
-- title:
--   Theorem 6 (exact part) — the Circuit SAT proof is perfectly complete, perfectly sound and a perfect proof of knowledge
-- statement:
--   Let $(K_{\mathrm{binding}},K_{\mathrm{hiding}},\mathrm{com},\mathrm{Topen},P_{01},V_{01})$ be a homomorphic proof commitment scheme whose message space $\mathcal M$ is cyclic of order $N\ge4$, with the homomorphic property, perfect binding, and perfectly complete and perfectly sound proofs that a commitment contains $0$ or $1$. Then the Circuit SAT proof $(K,P,V)$ of Figure 3, with common reference string $\sigma=ck$ for $(ck,xk)\leftarrow K_{\mathrm{binding}}$:
--
--   1. has **perfect completeness**, on keys output by $K_{\mathrm{binding}}$ and on keys output by $K_{\mathrm{hiding}}$;
--   2. has **perfect soundness**: on every key output by $K_{\mathrm{binding}}$, no proof for an unsatisfiable circuit is accepted;
--   3. is a **perfect proof of knowledge** if the scheme also has perfect extractability: on every $(ck,xk)$ output by $K_{\mathrm{binding}}$, the wires $w_i=[\mathrm{Ext}_{xk}(c_i)=1]$ extracted from any accepted proof satisfy the circuit.
--
--   $$\text{completeness}\ \wedge\ \text{soundness}\ \wedge\ \big(\text{perfect extractability}\Rightarrow\text{perfect knowledge extraction}\big).$$
--
--   Theorem 6 is the paper's NIZK proof for Circuit SAT; instantiated with the commitments of Sections 4 and 5 it gives the perfectly sound NIZK proofs for Circuit SAT of Corollaries 9 and 10.
--
--   **Formalization Note** Only the exact clauses of Theorem 6 are stated. "Computational zero-knowledge" and "computational non-erasure zero-knowledge" are dropped: they rest on the computational indistinguishability of binding and hiding keys; their exact core, perfect zero-knowledge on hiding keys (Lemma 8), is a separate mission. Every "for all adversaries, $\Pr=1$ / $\Pr=0$" is stated for every key in the support of the generator and every choice of the adversary. Perfect completeness is stated on keys of both modes; on binding keys it is Theorem 6's, on hiding keys Theorem 11's. $\mathcal M$ is `ZMod N` and `4 ≤ N` is the paper's restriction on p. 14 ("we focus on the case where the message space ... has order at least 4").
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14, Theorem 6 (exact part: perfect completeness, perfect soundness, perfect proof of knowledge)

import Mathlib
import Definitions.Def_GOSNIZK_CircuitSound_Protocol

namespace GOSNIZK.CircuitSound

/-- Theorem 6, exact part (Groth, Ostrovsky, Sahai, *New Techniques for Noninteractive
Zero-Knowledge*, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 14). For a homomorphic
proof commitment scheme with message space of order at least 4, perfect binding, and perfectly
complete and perfectly sound 0/1 proofs, the protocol of Figure 3 has perfect completeness (on keys
of either mode) and perfect soundness; if the scheme also has perfect extractability, it is a
perfect proof of knowledge. The computational zero-knowledge clauses are not formalized. -/
theorem theorem_6 {N : ℕ} {R C CK XK TK Rp Prf : Type} [AddCommGroup R] [Fintype R] [CommGroup C] [Fintype C]
    [Fintype Rp] [Nonempty Rp] (S : Scheme N R C CK XK TK Rp Prf)
    (hN : 4 ≤ N) (hhom : S.Homomorphic) (hbind : S.PerfectBinding)
    (hcomp01 : S.PerfectCompleteness01) (hsound01 : S.PerfectSoundness01) :
    S.CircuitPerfectCompleteness ∧ S.CircuitPerfectSoundness ∧
      (S.PerfectExtractability → S.CircuitPerfectKnowledgeExtraction) := by sorry

end GOSNIZK.CircuitSound
