-- Prove2me | Theorems.Thm_NoisyOWMPC_Supplement_theorem_E_10
-- name    : NoisyOWMPC.Supplement.theorem_E_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:09:39.756677+00:00
-- url     : https://prove2.me/theorems/9d7df866-78fe-4168-85ba-18582aceb3c3
-- title:
--   Theorem E.10 — malicious OWSC from a nontrivial core
-- statement:
--   Let $C : \mathcal X \to \mathcal Y$ have a nontrivial core, and assume an indistinguishability obfuscator and one-way functions. For every public polynomial-size target circuit $f(x; \rho)$ and every constant $a > 0$ there is an instantiation of Construction E.8 with Constructions F.2 and F.12 (polynomial numbers $m$ of sign rows and $M$ of release rows with $m + 1$, $M + 1$ powers of two, block length $N = m(2m^{16} + 1)$, a pad size, and a channel zero-knowledge proof of knowledge for $R_{\mathrm{cert}}$ with polynomial channel uses and running times) that realizes $f$ in Definition E.1 with a negligible correctness error and a security error
--   $$
--   \varepsilon_{\mathrm{sec}}(\lambda) \le \lambda^{-a} \qquad \text{for all sufficiently large } \lambda .
--   $$
--   The semi-honest and malicious sender errors are negligible. The protocol is Las Vegas, has a deterministic polynomial-time receiver, polynomial communication, and a sender implementable in polynomial time within negligible statistical distance; it needs no common reference string.
--
--   This holds for every admissible choice of the channel constants of Construction F.2, every family of public rational approximations of the channel probabilities, every expander family as in Corollary A.8 with $(c, \gamma) = (16, 2/5)$ and every polynomial-time Fig. 6 generator.
--
--   **Formalization Note** The printed bound "$\lambda^{-c}$" has no $c$ in scope; the proof (p.65) chooses $m$ with $qm^{-1/10} \le \lambda^{-(a+1)}$ and concludes that "the stated security bound follows for sufficiently large $\lambda$", so the bound is $\lambda^{-a}$. "No common reference string" holds by the model of Definition E.1, which has none.
--
--   Differences from the source:
--   - reading: security error at most λ^{−c} (c not bound in the statement) → security error ≤ λ^{−a} for all sufficiently large λ, a the theorem's constant; reason: the statement quantifies 'every constant a > 0' and the proof (p.65) makes qm^{−1/10} ≤ λ^{−(a+1)}, concluding 'the stated security bound follows for sufficiently large λ'
--   - encoding: 'Fix a posterior vector q*', the inputs a₀, a₁ of the core, the public rational approximations of §5, a Fig. 6 program → every choice (a, x*, y*) with IsF2Constants, every apx with IsApx and every generator with IsFig6Gen, quantified universally; the parameters m, M, the pad bound and the proof system existentially; reason: the paper leaves these choices open and the theorem asserts an instantiation exists
--   - generalization: the expander of Corollary A.8 with (c, γ, r) = (16, 2/5, 84) → every expander family satisfying the conclusion of Corollary A.8 for (c, γ) = (16, 2/5) (IsA8Family); reason: the paper's graph is one such family (as in the base Lemma 5.16)
--   - reading: 'polynomial communication and running time', 'deterministic receiver' → polynomial L and N_Π, a polynomial-time receiver (deterministic by the protocol syntax), and a polynomial-time sender within negligible statistical distance of the exact reference sender; reason: §5 Conventions, p.21: samplers are implemented within 2^{−λ}; the sender has polynomially many samplers
--   - encoding: 'needs no common reference string' → no separate clause; reason: Definition E.1's model has no common reference string, so the property holds for every protocol in it
--   - encoding: 'assume iO and one-way functions' → an IOScheme O with IsIO and OWFExists; reason: the base mission's encoding (as in Theorem 5.24)
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem E.10, p.65 (proof, p.65; Lemmas F.1, F.11, pp.67, 72)

import Mathlib
import Definitions.Def_NoisyOWMPC_Supplement_constructionE8
import Definitions.Def_NoisyOWMPC_Supplement_MalOWSC
import Definitions.Def_NoisyOWMPC_Supplement_releaseF2
import Definitions.Def_NoisyOWMPC_Supplement_selectorF12
import Definitions.Def_NoisyOWMPC_accessHalf
import Definitions.Def_NoisyOWMPC_IsA8Family
import Definitions.Def_NoisyOWMPC_OWFExists

namespace NoisyOWMPC.Supplement

/-- **Theorem E.10 (Malicious OWSC from a nontrivial core)** (Ishai, Lu, Zafar, *Non-Interactive
Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem E.10, p.65): "Let `C` have a nontrivial core, and assume iO
and one-way functions. For every public polynomial-size target circuit `f(x; ρ)` and every constant
`a > 0`, Construction E.8, instantiated with Constructions F.2 and F.12, realizes `f` in
Definition E.1 with negligible correctness error and security error at most `λ^{−c}`. The
semi-honest and malicious sender errors are negligible. The protocol is Las Vegas, has a
deterministic receiver and polynomial communication and running time, and needs no common reference
string."

Let `C : X → Y` have a nontrivial core, `O` be an iO scheme, and one-way functions exist. For every
public polynomial-size target circuit `f` (`F`), every constant `a > 0`, every choice of the channel
constants of Construction F.2 (`a₀, a₁, x*, q* = q_{y*}`), every family `apx` of public rational
upper approximations, and every expander family as in Corollary A.8 with `(c, γ) = (16, 2/5)`, there
are polynomial parameters `m` (sign rows, `m + 1` a power of two) and `M` (release rows, `M` odd,
`M + 1` a power of two) such that, with the selector of Construction F.12 on `[N]`,
`N = m(2m¹⁶ + 1)`, and the release test of Construction F.2 with `M` rows, for every
polynomial-time Fig. 6 generator there is a polynomial pad bound above which every pad size admits a
channel zero-knowledge proof of knowledge for `R_cert` with polynomial channel uses and running
times, and Construction E.8 then:
* realizes `f` in Definition E.1 with a negligible correctness error `ε_cor` and a security error
  `ε_sec ≤ λ^{−a}` for all large `λ`;
* has negligible semi-honest and malicious sender errors;
* is Las Vegas, with polynomial `L` and `N_Π`, a deterministic polynomial-time receiver, and a
  polynomial-time sender within negligible statistical distance of the exact reference sender.

**Formalization Note** The printed "`λ^{−c}`" has no `c` in scope; the theorem quantifies "every
constant `a > 0`" and its proof (p.65) makes `qm^{−1/10} ≤ λ^{−(a+1)}` and concludes "the stated
security bound follows for sufficiently large `λ`", so the bound is `λ^{−a}`. The constructions'
choices ("Fix …", p.67; the expander of Corollary A.8 with `(c, γ, r) = (16, 2/5, 84)`, p.68, p.73;
the rational approximations of §5 Conventions, p.21) are quantified universally; the parameters,
the pad bound and the proof system are existential ("there is an instantiation"). The Fig. 6
generator is quantified universally as in Theorem 5.24. "No common reference string" holds by the
model of Definition E.1, which has none. -/
theorem theorem_E_10 {X Yc : Type} [Fintype X] [Fintype Yc] (C : DMC X Yc)
    (hC : HasNontrivialCore C) (O : IOScheme) (hO : O.IsIO) (hOWF : OWFExists)
    (F : Functionality 1) (hF : F.IsPolyCircuit) (a : ℝ) (ha : 0 < a) :
    ∀ (ac : Bool → X) (xstar : Bool) (ystar : Yc), IsF2Constants C ac xstar ystar →
    ∀ apx : ℕ → ∀ i : Fin 1, X → oneY Yc i → ℚ, IsApx (oneC C) apx →
    ∀ Gr : (M ℓ G : ℕ) → LayeredGraph M, IsA8Family Gr 16 (2 / 5) →
      ∃ m M : ℕ → ℕ, PolyParam m ∧ (∀ lam, ∃ e : ℕ, m lam + 1 = 2 ^ e) ∧
        PolyParam M ∧ (∀ lam, Odd (M lam) ∧ ∃ e : ℕ, M lam + 1 = 2 ^ e) ∧
        let Rt := releaseF2 C ac ystar apx M Gr
        let St := selectorF12 m Gr
        ∀ gen : ProgGen (halvesE8 Rt St) F, IsFig6Gen (halvesE8 Rt St) F gen →
          ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
            ∃ Z : ChannelZK X Yc (txLen (halvesE8 Rt St) F O gen s),
              Z.IsZKPoK C (Rcert Rt St F O gen s) ∧
              let P := constructionE8 Rt St F O gen s Z
              ∃ εcor εsec : ℕ → ℝ, Negligible εcor ∧
                (∃ lam₀ : ℕ, ∀ lam ≥ lam₀, εsec lam ≤ (lam : ℝ) ^ (-a)) ∧
                IsMalOWSC P C εcor εsec ∧
                (∃ εS : ℕ → ℝ, Negligible εS ∧ P.SecErr (oneC C) true ∅ εS ∧
                  MalSenderErr P C εS) ∧
                P.LasVegas (oneC C) ∧ PolyBounded P.L ∧ PolyBounded P.N ∧
                (∃ Ssam : CoinAlg, Ssam.IsPPT ∧ ∃ ν : ℕ → ℝ, Negligible ν ∧
                  ∀ (lam : ℕ) (x : Fin (F.lx lam) → Bool),
                    sdPush (unifW (Fin (Ssam.coins lam) → Bool))
                        (fun ρ => Ssam.run lam (LaconicBarrier.bits x) ρ) (P.wS lam)
                        (fun r => QAdvFew.PoQOracle.tup [P.encRS lam r,
                          LaconicBarrier.bits (P.send lam x r).1, wordEnc X (P.send lam x r).2]) ≤
                      ν lam) ∧
                LaconicBarrier.PolyTimeOn
                  (ι := (lam : ℕ) × (Fin (P.L lam) → Bool) × (Fin (P.N lam) → Yc))
                  (fun z => [LaconicBarrier.unary z.1, LaconicBarrier.bits z.2.1, wordEnc Yc z.2.2])
                  (fun z => optEnc (P.recv z.1 0 z.2.1 z.2.2)) := by sorry

end NoisyOWMPC.Supplement
