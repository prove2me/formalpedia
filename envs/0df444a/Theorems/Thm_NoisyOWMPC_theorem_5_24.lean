-- Prove2me | Theorems.Thm_NoisyOWMPC_theorem_5_24
-- name    : NoisyOWMPC.theorem_5_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:06:27.536222+00:00
-- url     : https://prove2.me/theorems/9e7ed367-03de-44e1-b090-99815792c987
-- title:
--   Theorem 5.24 — one-way MPC from noise preservation
-- statement:
--   Let $\mathbf C=(C_1,\dots,C_k)$, $k\ge1$, be a product broadcast channel satisfying noise preservation with bits $\beta$ (Definition 4.5), let $i\mathcal O$ be an indistinguishability obfuscator (Definition 3.2), assume one-way functions exist, and let $F=(f_i)$ be polynomial target circuits and $\mathrm{apx}$ rational approximations of the channel within $2^{-\lambda}$. Construction 5.23 instantiated with the access tests of Construction 5.6, the release tests of Construction 5.11 and the subset selector of Construction 5.17 satisfies:
--
--   1. **(a) the bounds of Theorem 5.25.** There are a polynomial $n_0$ and a constant $K$ such that for all admissible $M\ge n_0^6$ and $N\ge n_0^{20}$ there are negligible access errors $\alpha,\delta_{\mathrm{acc}}$ (zero when $k=1$) such that for every polynomial-time Fig. 6 generator and every large enough polynomial pad size, with $\eta=KM^{-3}$, $\delta_{\mathrm{rel}}=KM^{-1/10}$, $\alpha_{\mathrm{sel}}=b_N=2e^{-2r_N^2/N}$ and $\delta_{\mathrm{sel}}=KN^{-0.013}$: the correctness error is at most $k\alpha+q(N\eta+\alpha_{\mathrm{sel}})+\mathrm{negl}(\lambda)$, every receiver-only coalition $J$ has error
--   $$(k-|J|)(\alpha+\delta_{\mathrm{acc}})+Nq_J\delta_{\mathrm{rel}}+q_J\delta_{\mathrm{sel}}+qN\eta+q_{-J}\alpha_{\mathrm{sel}}+\mathrm{negl}(\lambda),$$
--   and every coalition $\{S\}\cup J$ has error $(k-|J|)\alpha+q_{-J}(N\eta+\alpha_{\mathrm{sel}})+\mathrm{negl}(\lambda)$.
--   2. **(b)** For every $c>0$ the public parameters $M,N$ can be chosen polynomially so that the correctness error and every coalition's security error are $O(\lambda^{-c})$.
--   3. **(c)** The protocol is Las Vegas.
--   4. **(d)** It uses exactly $\mathbf 1[k>1]\,kM^3+2|\mathcal X|qNM^9$ channel uses.
--   5. **(e)** It is efficient: polynomial lengths, a sender implementable in polynomial time within $2^{-\lambda}$, deterministic polynomial-time receivers.
--
--   This is the paper's main theorem: noise preservation, together with iO and one-way functions, suffices for one-way secure computation of every randomized functionality over a noisy broadcast channel.
--
--   Differences from the source:
--   - generalization: Construction 5.23 with the paper's (unspecified) circuit for Fig. 6, 'padded to the common size' → every deterministic polynomial-time generator of a circuit computing Fig. 6's function, and every polynomial pad size above some s₀ (Las Vegas and efficiency: every size the program fits); reason: the paper fixes no circuit; its implementation is one such generator
--   - generalization: fixed public rational upper approximations within 2^{−λ}, chosen deterministically → every polynomial-time computable family apx with C ≤ apx ≤ C + 2^{−λ}; reason: the paper's fixed choice is one such family; the analysis uses only these bounds (§5 Conventions, p.21)
--   - reading: 'with the correctness and coalition simulation bounds of Theorem 5.25' (which assumes all seed lengths at least the input length of F) → ∃ polynomial n₀: the bounds for every admissible M ≥ n₀⁶ and N ≥ n₀²⁰; reason: the paper's proof (p.31) secures the seed-length condition by these choices, n₀ = λ + n(λ)
--   - reading: errors of Theorem 5.22 and Lemma 5.16: access errors negligible, η, δ_rel = O(M^{−1/10}), δ_sel = O(N^{−0.013}); 'all errors are O(λ^{−c})' → negligible α, δ_acc; η = K M^{−3}, δ_rel = K M^{−1/10}, δ_sel = K N^{−0.013} with one constant K; O(λ^{−c}) as ≤ K′λ^{−c} for large λ; reason: standard reading of O; η = K₁M^{−3} by Lemma 5.12
--   - encoding: negl(λ) in the coalition bounds → the distinguisher-dependent negligible term of ≈^c; correctness has one negligible ν₀; reason: Definition 4.2 (security via ≈^c) and §3
--   - encoding: nonuniform PPT distinguishers and adversaries → polynomial-size deterministic circuit families; reason: randomized nonuniform adversaries are matched by fixing their best coins
--   - encoding: samplers implemented within statistical error 2^{−λ} → exact reference distributions; efficiency clauses ask for a polynomial-time sampler within 2^{−λ}; reason: the paper's own convention: 'The distributions above are exact reference distributions' (p.24)
--   - encoding: 'a public order', 'fixed-length encodings', 'an odd integer nearest to N^{0.36}' → access cells first, then release cells in order (i, j, v); fixed symbol encodings; the smaller odd integer on a tie; reason: conventions the paper leaves open; no instance changes
--   - encoding: 'realizes the target functions in Definition 4.2' → correctness and security errors plus the efficiency clause (e) of Definition 4.2's syntax; reason: Definition 4.2 requires polynomial-time parties
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
--   - encoding: Definition 3.2: iO returns a circuit with 'polynomially bounded description'; obfuscations 'padded to a fixed public length' (p.21) → IOScheme carries a public length bound len(λ, n, s), polynomial and computable in polynomial time, on every obfuscated description; reason: every obfuscator with polynomially bounded descriptions has such a bound; it fixes the public transmission length
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 5.24, p.30 (with the bounds of Theorem 5.25, p.31)

import Mathlib
import Definitions.Def_NoisyOWMPC_construction
import Definitions.Def_NoisyOWMPC_concreteHalves
import Definitions.Def_NoisyOWMPC_SecErr
import Definitions.Def_NoisyOWMPC_NoisePreserving
import Definitions.Def_NoisyOWMPC_OWFExists

namespace NoisyOWMPC

/-- **Theorem 5.24 (One-way MPC from noise preservation)** (Ishai, Lu, Zafar, *Non-Interactive
Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem 5.24, p.30, with the bounds of Theorem 5.25, p.31): "Under
Definition 4.5, iO, and one-way functions, Construction 5.23 instantiated with the tests of Theorem
5.22 and the subset selector of Lemma 5.16 realizes the target functions in Definition 4.2, with the
correctness and coalition simulation bounds of Theorem 5.25. For every fixed `c > 0`, the public
parameters can be chosen polynomially so that all errors are `O(λ^{−c})`. The raw test words use
`1[k > 1] kM³ + 2|X|qNM⁹` channel uses."

For every product broadcast channel with `k ≥ 1` receivers and noise-preservation bits `β`, every
iO scheme `O`, one-way functions existing, every polynomial-size family of target circuits `F`
and every family `apx` of rational upper approximations, `Π = construction (concreteHalves …) F O
gen s` satisfies:
* (a) the bounds of Theorem 5.25 for every admissible `M`, `N` above the seed-length thresholds
  `M ≥ n₀⁶`, `N ≥ n₀²⁰`, every polynomial-time generator of Fig. 6 and every large enough
  polynomial pad size, with `η = K M^{−3}`, `δ_rel = K M^{−1/10}`, `α_sel = b_N`,
  `δ_sel = K N^{−0.013}` and negligible access errors `α`, `δ_acc` (zero when `k = 1`);
* (b) for every `c > 0` some admissible `M`, `N` make the correctness error and every coalition's
  security error `O(λ^{−c})`;
* (c) the protocol is Las Vegas whenever the program fits the pad size;
* (d) it uses exactly `1[k > 1] kM³ + 2|X|qNM⁹` channel uses;
* (e) it is efficient (polynomial lengths, sender implementable within `2^{−λ}`, polynomial-time
  receivers).

**Formalization Note** `O(·)` is a constant `K` fixed before the parameters (it depends only on the
channel and `β`); the parameters `M`, `N` and the pad size `s` are public polynomial parameters
(`PolyParam`: computed from `1^λ` in polynomial time, Definition 4.2, p.18); negligible terms of
the receiver-coalition and sender-coalition bounds are those of `≈^c` in `Protocol.SecErr`; the correctness bound carries one negligible `ν₀`. -/
theorem theorem_5_24 {k : ℕ} (hk : 1 ≤ k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (β : ∀ i, X → Y i → Bool)
    (hβ : NoisePreserving C β) (O : IOScheme) (hO : O.IsIO) (hOWF : OWFExists)
    (F : Functionality k) (hF : F.IsPolyCircuit) (apx : ℕ → ∀ i, X → Y i → ℚ)
    (hapx : IsApx C apx) :
    -- (a) the bounds of Theorem 5.25
    (∃ n₀ : ℕ → ℕ, PolyBounded n₀ ∧ ∃ K : ℝ, 0 < K ∧
      ∀ M N : ℕ → ℕ, AdmissibleM M → AdmissibleN N →
        (∀ lam, n₀ lam ^ 6 ≤ M lam) → (∀ lam, n₀ lam ^ 20 ≤ N lam) →
        ∃ α δacc : ℕ → ℝ, Negligible α ∧ Negligible δacc ∧
          (k = 1 → ∀ lam, α lam = 0 ∧ δacc lam = 0) ∧
          ∀ gen : ProgGen (concreteHalves C β apx M N) F,
            IsFig6Gen (concreteHalves C β apx M N) F gen →
            ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
              (∃ ν₀ : ℕ → ℝ, Negligible ν₀ ∧
                (construction (concreteHalves C β apx M N) F O gen s).CorrErr C (fun lam =>
                  (k : ℝ) * α lam + (F.qOf Finset.univ lam : ℝ) *
                    ((N lam : ℝ) * (K / (M lam : ℝ) ^ 3) + bN (N lam)) + ν₀ lam)) ∧
              (∀ J : Finset (Fin k),
                (construction (concreteHalves C β apx M N) F O gen s).SecErr C false J (fun lam =>
                  ((k : ℝ) - J.card) * (α lam + δacc lam) +
                    (N lam : ℝ) * (F.qOf J lam : ℝ) * (K * (M lam : ℝ) ^ (-(1 / 10 : ℝ))) +
                    (F.qOf J lam : ℝ) * (K * (N lam : ℝ) ^ (-(13 / 1000 : ℝ))) +
                    (F.qOf Finset.univ lam : ℝ) * (N lam : ℝ) * (K / (M lam : ℝ) ^ 3) +
                    ((F.qOf Finset.univ lam : ℝ) - F.qOf J lam) * bN (N lam))) ∧
              (∀ J : Finset (Fin k),
                (construction (concreteHalves C β apx M N) F O gen s).SecErr C true J (fun lam =>
                  ((k : ℝ) - J.card) * α lam +
                    ((F.qOf Finset.univ lam : ℝ) - F.qOf J lam) *
                      ((N lam : ℝ) * (K / (M lam : ℝ) ^ 3) + bN (N lam))))) ∧
    -- (b) errors O(λ^{−c}) for chosen polynomial parameters
    (∀ c : ℝ, 0 < c → ∃ M N : ℕ → ℕ, AdmissibleM M ∧ AdmissibleN N ∧
      ∀ gen : ProgGen (concreteHalves C β apx M N) F,
        IsFig6Gen (concreteHalves C β apx M N) F gen →
        ∃ s₀ : ℕ → ℕ, PolyBounded s₀ ∧ ∀ s : ℕ → ℕ, PolyParam s → (∀ lam, s₀ lam ≤ s lam) →
          ∃ ε : ℕ → ℝ, (∃ K' : ℝ, ∃ lam₀ : ℕ, ∀ lam ≥ lam₀, ε lam ≤ K' * (lam : ℝ) ^ (-c)) ∧
            (construction (concreteHalves C β apx M N) F O gen s).CorrErr C ε ∧
            ∀ (withS : Bool) (J : Finset (Fin k)),
              (construction (concreteHalves C β apx M N) F O gen s).SecErr C withS J ε) ∧
    -- (c) Las Vegas
    (∀ M N : ℕ → ℕ, AdmissibleM M → AdmissibleN N →
      ∀ gen : ProgGen (concreteHalves C β apx M N) F,
        IsFig6Gen (concreteHalves C β apx M N) F gen →
        ∀ s : ℕ → ℕ, (∀ lam x c, (gen lam x c).base.gates.length ≤ s lam) →
          (construction (concreteHalves C β apx M N) F O gen s).LasVegas C) ∧
    -- (d) channel uses
    (∀ (M N : ℕ → ℕ) (gen : ProgGen (concreteHalves C β apx M N) F) (s : ℕ → ℕ) (lam : ℕ),
      (construction (concreteHalves C β apx M N) F O gen s).N lam =
        (if 1 < k then k * M lam ^ 3 else 0) +
          2 * Fintype.card X * F.qOf Finset.univ lam * N lam * M lam ^ 9) ∧
    -- (e) efficiency
    (∀ M N : ℕ → ℕ, AdmissibleM M → AdmissibleN N →
      ∀ gen : ProgGen (concreteHalves C β apx M N) F,
        IsFig6Gen (concreteHalves C β apx M N) F gen →
        ∀ s : ℕ → ℕ, PolyParam s → (∀ lam x c, (gen lam x c).base.gates.length ≤ s lam) →
          (construction (concreteHalves C β apx M N) F O gen s).IsEfficient) := by sorry

end NoisyOWMPC
