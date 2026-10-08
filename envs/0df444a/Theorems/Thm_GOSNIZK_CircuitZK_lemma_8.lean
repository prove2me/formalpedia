-- Prove2me | Theorems.Thm_GOSNIZK_CircuitZK_lemma_8
-- name    : GOSNIZK.CircuitZK.lemma_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:26:28.494281+00:00
-- url     : https://prove2.me/theorems/c3e0d880-b3c2-4eb2-b0aa-f5253b8743a2
-- title:
--   Lemma 8 — on a perfectly hiding key the Circuit SAT proof of Figure 3 is perfect zero-knowledge
-- statement:
--   Let the message space of the commitment scheme have order $N \ge 4$, and let the scheme be homomorphic, with perfect trapdoor opening, perfect trapdoor opening indistinguishability and perfect witness indistinguishability. Run the Circuit SAT proof of Figure 3 with the common reference string $\sigma = ck$ drawn from $K_{\mathrm{hiding}}$ (the generator $S_\sigma$), and take the simulator $S_1 = K_{\mathrm{hiding}}$, which also returns $\tau = tk$, together with $S_2$.
--
--   Then for every adaptive adversary $A$, which reads $\sigma$ and then submits circuit-witness pairs $(C, w)$ to its oracle, each chosen after seeing the earlier answers,
--   $$\Pr\big[\sigma \leftarrow S_\sigma : A^{P(\sigma,\cdot,\cdot)}(\sigma) = 1\big] = \Pr\big[(\sigma, \tau) \leftarrow S_1 : A^{S(\sigma,\tau,\cdot,\cdot)}(\sigma) = 1\big],$$
--   where both oracles answer *failure* on pairs with $C(w) \ne 1$. That is, $(S_\sigma, P, V)$ is perfect (adaptive multi-theorem) zero-knowledge.
--
--   This is the zero-knowledge half of Theorem 11, the first perfect non-interactive zero-knowledge argument for every language in NP; with the key indistinguishability of the commitment scheme it also gives the computational zero-knowledge of the proof of Figure 3 on binding keys (Theorem 6).
--
--   **Formalization Note** The statement is the equality of the two output laws of $A$. Adversaries range over all well-founded query trees with fair coins, which contains every polynomial-time adversary; no running-time bound is imposed on them or on the simulator. The simulator is the specific $S_2$ of the proof, which does not see the witness. The second sentence of Lemma 8 (perfect non-erasure zero-knowledge) is not part of this statement.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 15, Lemma 8 (first sentence); its zero-knowledge part is the perfect zero-knowledge claim of Theorem 11, p. 16; definition of perfect zero-knowledge, p. 5

import Mathlib
import Definitions.Def_GOSNIZK_CircuitZK_ZKGame

namespace GOSNIZK.CircuitZK

/-- Lemma 8, first sentence (Groth, Ostrovsky, Sahai, J. ACM 59(3) (2012), authors' version of March 7, 2011,
p. 15; the zero-knowledge half of Theorem 11, p. 16): `(S_σ, P, V)`, where `S_σ` is `K_hiding` restricted to the
first part of its output, has perfect (adaptive multi-theorem) zero-knowledge, with the simulator `S₁ = K_hiding`
and `S₂ = simulate`. For every adaptive adversary `A` that reads `σ = ck` and queries pairs `(C, w)`,
`Pr[σ ← S_σ : A^{P(σ,·,·)}(σ) = 1] = Pr[(σ, τ) ← S₁ : A^{S(σ,τ,·,·)}(σ) = 1]`, as an equality of output laws. -/
theorem lemma_8 {N : ℕ} {R C CK XK TK Rp Pf : Type} [AddCommGroup R] [CommGroup C]
    [Fintype R] [Nonempty R] [Fintype Rp] [Nonempty Rp] (hN : 4 ≤ N)
    (S : Scheme N R C CK XK TK Rp Pf) (hhom : S.Homomorphic) (hTO : S.PerfectTrapdoorOpening)
    (hTOI : S.PerfectTrapdoorOpeningIndist) (hWI : S.PerfectWI)
    (A : CK → Adv Query (Option (Proof C Pf))) :
    (S.Khide.bind fun kt => (A kt.1).run (realOracle S kt.1)) =
      (S.Khide.bind fun kt => (A kt.1).run (simOracle S kt.1 kt.2)) := by sorry

end GOSNIZK.CircuitZK
