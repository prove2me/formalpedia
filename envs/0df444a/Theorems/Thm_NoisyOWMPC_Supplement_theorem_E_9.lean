-- Prove2me | Theorems.Thm_NoisyOWMPC_Supplement_theorem_E_9
-- name    : NoisyOWMPC.Supplement.theorem_E_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:08:30.192588+00:00
-- url     : https://prove2.me/theorems/e910bbf6-6168-46e9-8a48-c4b89eb89bb7
-- title:
--   Theorem E.9 — malicious OWSC from verifiable tests and selectors
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ have a nontrivial core. Fix a verifiable release test with channel-input length $n_{\mathrm{rel}}$ and errors $(\eta, \delta_{\mathrm{rel}}, \delta_{\mathrm{send}})$, a verifiable selector on $[N]$ with input-bias bound $\delta_{\mathrm{send}}$ and errors $(\alpha_{\mathrm{sel}}, \beta_{\mathrm{sel}}, \delta_{\mathrm{sel}})$, a public polynomial-size target circuit $f : \{0,1\}^{\ell_x} \times \{0,1\}^q \to \{0,1\}^{\ell}$, an indistinguishability obfuscator and an injective one-way function whose input length $n(\lambda)$ is at most both seed lengths. For every polynomial-time Fig. 6 generator, every large enough polynomial pad size and every channel zero-knowledge proof of knowledge for $R_{\mathrm{cert}}$ with $n_{\mathrm{ZK}}$ channel uses, Construction E.8 realizes $f$ in Definition E.1, is Las Vegas, and has the errors
--
--   1. correctness and semi-honest sender security: at most $q(N\eta + \alpha_{\mathrm{sel}}) + \mathrm{negl}(\lambda)$;
--   2. receiver security: at most $qN\delta_{\mathrm{rel}} + q\delta_{\mathrm{sel}} + qN\eta + \mathrm{negl}(\lambda)$;
--   3. malicious-sender security: at most $q\beta_{\mathrm{sel}} + \mathrm{negl}(\lambda)$.
--
--   It uses exactly
--   $$
--   qN n_{\mathrm{rel}} + n_{\mathrm{ZK}}
--   $$
--   noisy channel uses and $L$ noiseless bits, the fixed transmission length of the obfuscated program; its lengths are polynomial, its receiver runs in polynomial time, and its sender is implementable in polynomial time within statistical distance $(q + qN)2^{-\lambda}$.
--
--   The theorem upgrades the semi-honest main construction to security against a malicious sender: the zero-knowledge proof certifies a valid program, and robust balance keeps the selected coins fair for every transmitted word.
--
--   **Formalization Note** The $\mathrm{negl}(\lambda)$ terms of the security bounds are those of $\approx^c$; the correctness bound has an explicit negligible term. $R_{\mathrm{cert}}$ depends on the generator and the pad size, so the proof system is quantified after them.
--
--   Differences from the source:
--   - generalization: 'assuming iO and one-way functions', with the injective OWF F of §5 whose input length bounds the seed lengths → every iO scheme O and every injective one-way function Finj with Finj.n at most both seed lengths; reason: Theorem 3.4 gives such an F from iO and one-way functions; the paper's F is one of them (as in the base Theorem 5.25)
--   - generalization: the paper's program padded to 'a common public polynomial size' → every polynomial-time Fig. 6 generator and every polynomial pad size above some s₀; reason: the paper's implementation is one such generator and size (as in the base Theorem 5.25)
--   - encoding: negl(λ) in the security bounds → the distinguisher-dependent negligible term of ≈^c in SecErr and MalSenderErr; an explicit negligible ν₀ in the correctness bound; reason: Definitions 4.2 and E.1
--   - reading: 'Construction E.8 realizes f in Definition E.1' (the syntax of Definition 4.2) → adds polynomial L and N_Π, a polynomial-time receiver, and a polynomial-time sender within statistical distance (q + qN)·2^{−λ} of the exact reference sender; reason: each of the qN + q sampled states comes from a sampler within 2^{−λ} (§5 Conventions, p.21); masks, obfuscator tape and prover coins are uniform (as in the base Theorem 5.25)
--   - encoding: Construction 5.23 with one receiver; 'there is no access test' → the published construction with the trivial access test (channel-input length 0, one state); reason: Definition 5.2 for k = 1
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem E.9, p.64 (proof, pp.65–67)

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_constructionE8
import Definitions.Def_NoisyOWMPC_Supplement_MalOWSC
import Definitions.Def_NoisyOWMPC_Supplement_NontrivialCore
import Definitions.Def_NoisyOWMPC_KeyedFamily

namespace NoisyOWMPC.Supplement

/-- **Theorem E.9 (Malicious OWSC from verifiable tests and selectors)** (Ishai, Lu, Zafar,
*Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027
submission (manuscript sha256 3a9569fa…), Theorem E.9, p.64): "Assuming iO and one-way functions,
Construction E.8 realizes `f` in Definition E.1 and is Las Vegas, with the following errors.
• Correctness and semi-honest sender security: at most `q(Nη + α_sel) + negl(λ)`.
• Receiver security: at most `qNδ_rel + qδ_sel + qNη + negl(λ)`.
• Malicious-sender security: at most `qβ_sel + negl(λ)`.
The protocol uses `qNn_rel + n_ZK` noisy channel uses and `L` noiseless bits."

Fix a channel `C : X → Y` with a nontrivial core (Definition E.2), a verifiable release test with
channel-input length `n_rel` and errors `(η, δ_rel, δ_send)`, a verifiable selector on `[N]` with
input-bias bound `δ_send` and errors `(α_sel, β_sel, δ_sel)`, a public polynomial-size target
circuit `f : {0,1}^{ℓ_x} × {0,1}^q → {0,1}^ℓ`, an iO scheme and an injective one-way function whose
input length `n(λ)` is at most both seed lengths. For every polynomial-time Fig. 6 generator, every
large enough polynomial pad size, and every channel zero-knowledge proof of knowledge for `R_cert`,
Construction E.8 satisfies:
* correctness error `q(Nη + α_sel) + ν₀` for a negligible `ν₀`;
* semi-honest sender (`{S}`) security error `q(Nη + α_sel)`, receiver (`{1}`) security error
  `qNδ_rel + qδ_sel + qNη`, malicious-sender security error `qβ_sel`, each with the negligible term
  of `≈^c`;
* Las Vegas; exactly `qN n_rel + n_ZK` channel uses and `L` noiseless bits (the transmission length
  of the obfuscated program);
* the syntax of Definition 4.2: polynomial `L` and `N_Π`, a polynomial-time receiver, and a
  polynomial-time sender within statistical distance `(q + qN)2^{−λ}` of the exact reference sender.

**Formalization Note** "Assuming iO and one-way functions" is an iO scheme `O` and an injective one-way
function `Finj` (Theorem 3.4), whose input length all seed lengths exceed (Construction E.8, p.64).
The program is padded to `s` gates for every public polynomial `s` above some `s₀` (§5 Conventions,
p.21); `R_cert` depends on the generator and the pad size, so the proof system is quantified after
them. The sender's `q + qN` sampled states each come from a sampler within `2^{−λ}` (§5 Conventions,
p.21); its masks, obfuscator tape and prover coins are uniform. -/
theorem theorem_E_9 {X Yc : Type} [Fintype X] [Fintype Yc] (C : DMC X Yc)
    (hC : HasNontrivialCore C) (nrel N : ℕ → ℕ) (hpar : PolyParam nrel ∧ PolyParam N)
    (R : VerReleaseTest X Yc nrel) (S : VerSelector N)
    (η δrel δsend αsel βsel δsel : ℕ → ℝ) (hR : R.IsVerRelease C η δrel δsend)
    (hS : S.IsVerSelector δsend αsel βsel δsel) (F : Functionality 1) (hF : F.IsPolyCircuit)
    (O : IOScheme) (hO : O.IsIO) (Finj : KeyedFamily) (hFinj : Finj.IsInjOWF)
    (hseed : (∀ lam, Finj.n lam ≤ R.κ lam) ∧ ∀ lam, Finj.n lam ≤ S.κ lam) :
    ∀ gen : ProgGen (halvesE8 R S) F, IsFig6Gen (halvesE8 R S) F gen →
      ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
        ∀ Z : ChannelZK X Yc (txLen (halvesE8 R S) F O gen s),
          Z.IsZKPoK C (Rcert R S F O gen s) →
          (∃ ν₀ : ℕ → ℝ, Negligible ν₀ ∧
            (constructionE8 R S F O gen s Z).CorrErr (oneC C) (fun lam =>
              (F.r 0 lam : ℝ) * ((N lam : ℝ) * η lam + αsel lam) + ν₀ lam)) ∧
          (constructionE8 R S F O gen s Z).SecErr (oneC C) true ∅ (fun lam =>
            (F.r 0 lam : ℝ) * ((N lam : ℝ) * η lam + αsel lam)) ∧
          (constructionE8 R S F O gen s Z).SecErr (oneC C) false Finset.univ (fun lam =>
            (F.r 0 lam : ℝ) * (N lam : ℝ) * δrel lam + (F.r 0 lam : ℝ) * δsel lam +
              (F.r 0 lam : ℝ) * (N lam : ℝ) * η lam) ∧
          MalSenderErr (constructionE8 R S F O gen s Z) C (fun lam => (F.r 0 lam : ℝ) * βsel lam) ∧
          (constructionE8 R S F O gen s Z).LasVegas (oneC C) ∧
          (∀ lam, (constructionE8 R S F O gen s Z).N lam =
            F.r 0 lam * N lam * nrel lam + Z.nZK lam) ∧
          (∀ lam, (constructionE8 R S F O gen s Z).L lam = txLen (halvesE8 R S) F O gen s lam) ∧
          PolyBounded (constructionE8 R S F O gen s Z).L ∧
          PolyBounded (constructionE8 R S F O gen s Z).N ∧
          (∃ Ssam : CoinAlg, Ssam.IsPPT ∧ ∀ (lam : ℕ) (x : Fin (F.lx lam) → Bool),
            sdPush (unifW (Fin (Ssam.coins lam) → Bool))
                (fun ρ => Ssam.run lam (LaconicBarrier.bits x) ρ)
                ((constructionE8 R S F O gen s Z).wS lam)
                (fun r => QAdvFew.PoQOracle.tup [(constructionE8 R S F O gen s Z).encRS lam r,
                  LaconicBarrier.bits ((constructionE8 R S F O gen s Z).send lam x r).1,
                  wordEnc X ((constructionE8 R S F O gen s Z).send lam x r).2]) ≤
              ((F.r 0 lam : ℝ) + (F.r 0 lam : ℝ) * (N lam : ℝ)) * (2 : ℝ) ^ (-(lam : ℤ))) ∧
          LaconicBarrier.PolyTimeOn
            (ι := (lam : ℕ) × (Fin ((constructionE8 R S F O gen s Z).L lam) → Bool) ×
              (Fin ((constructionE8 R S F O gen s Z).N lam) → Yc))
            (fun z => [LaconicBarrier.unary z.1, LaconicBarrier.bits z.2.1, wordEnc Yc z.2.2])
            (fun z => optEnc ((constructionE8 R S F O gen s Z).recv z.1 0 z.2.1 z.2.2)) := by sorry

end NoisyOWMPC.Supplement
