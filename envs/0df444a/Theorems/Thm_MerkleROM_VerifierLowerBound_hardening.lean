-- Prove2me | Theorems.Thm_MerkleROM_VerifierLowerBound_hardening
-- name    : MerkleROM.VerifierLowerBound.hardening
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T22:33:55.08167+00:00
-- url     : https://prove2.me/theorems/c2bb5010-25ab-4504-b535-636e54ec03f1
-- title:
--   Lemma 5.1 — Hardening
-- statement:
--   Let $\Sigma$ be an efficient family in the source's polynomial oracle and vector-length regime, with $n=\Omega(\lambda)$. Put $p=Q+2kn+n^3$. For all sufficiently large $\lambda$, every fixed commitment $c$ and consistent starting table $T_0$ have all of the following properties for Algorithm 1:
--
--   $$\#\mathrm{queries}\le(3pn^2\lambda+1)(p+k)\le4p^2n^2\lambda,$$
--
--   $$T_{\mathrm{out}}=T_0\mathbin{+\!+}\mathrm{received\ answers},\qquad \mathrm{status}=\mathrm{hard}\Longrightarrow T_{\mathrm{out}}\text{ is }p\text{-hard},$$
--
--   $$\Pr_{R\text{ uniform extending }T_0}[\mathrm{status}=\mathrm{fail}]\le2^{-n\lambda}.$$
--
--   The procedure is realized by one deterministic oracle tree with exactly the recorded query transcript. The commitment and table in the probability statement are fixed before the extending oracle is sampled. This supplies the uniform fixed-input estimate used in the protocol error analysis.
--
--   Differences from the source:
--   - encoding: asymptotic cryptographic parameter regime → existential threshold before all sufficiently large security parameters; no polynomial degree fixed; reason: finite initial changes preserve security, and n=Omega(lambda) supplies positive growing vector length
--   - encoding: partial query-answer table as a set → a consistent list with repetitions recording each received answer; reason: consistency and extension depend on the underlying entries, while query complexity counts repetitions
--   - generalization: transcript-normalized verifier in Section 5 → the original accepting-transcript relation of any deterministic verifier; reason: Fact 1 identifies this relation with the normalized verifier; every source normalized instance is included
--   - generalization: the secure vector-commitment setting of Section 5 → only the explicitly stated efficiency or security properties needed by this local result; reason: the procedure and its estimates depend on finite oracle access and accepting transcripts, not on completeness or position binding; every secure source instance satisfies these hypotheses
-- source:
--   Miranda Christ, Oliver Korten, Tal Malkin, Noam Mazor, Shyamal Patel, STOC 2027 submission #1169 (October 2026), Merkle Trees Minimize Verifier Complexity in the ROM, p. 17, Lemma 5.1. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1169.pdf

import Definitions.Def_MerkleROM_VerifierLowerBound_protocol
import Definitions.Def_MerkleROM_VerifierLowerBound_product

set_option autoImplicit false
noncomputable section

namespace MerkleROM.VerifierLowerBound

theorem hardening (F : SchemeFamily) (n : ℕ → ℕ)
    (hF : Efficient F) (htheta : OracleLengths F.theta)
    (hn : PolynomiallyBounded n) (hnl : OmegaSecurity n) :
    ∃ N, ∀ l ≥ N,
      let S := F.scheme l (n l)
      let k := F.verifyQueries l (n l)
      let p := F.commitQueries l (n l) + 2*k*n l + (n l)^3
      ∀ (c : Bits (F.size l (n l))) (T : Table (Bits (F.theta l)) (Bits l)),
      Consistent T →
      ((3*p*(n l)^2*l+1)*(p+k) ≤ 4*p^2*(n l)^2*l) ∧
      (∀ R, (harden S k p c T R).queries.length ≤ (3*p*(n l)^2*l+1)*(p+k)) ∧
      (∃ a : Tree (Bits (F.theta l)) (Bits l) (HardenResult (F.theta l) l),
        ∀ R, a.run R = harden S k p c T R ∧
          a.transcript R = (harden S k p c T R).queries) ∧
      (∀ R, (harden S k p c T R).table = T ++ (harden S k p c T R).queries) ∧
      (∀ R, (harden S k p c T R).status = .hard →
        Hard S k p c (harden S k p c T R).table) ∧
      probability (tableLaw T) (fun R => (harden S k p c T R).status = .fail) ≤
        (2 : ℝ)^(-((n l*l : ℕ) : ℤ)) := by sorry

end MerkleROM.VerifierLowerBound
