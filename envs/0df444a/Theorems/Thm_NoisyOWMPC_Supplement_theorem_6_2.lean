-- Prove2me | Theorems.Thm_NoisyOWMPC_Supplement_theorem_6_2
-- name    : NoisyOWMPC.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:05:50.187385+00:00
-- url     : https://prove2.me/theorems/4d57fc24-9ce7-4ed7-a7be-78738f261b2b
-- title:
--   Theorem 6.2 — necessity of noise preservation
-- statement:
--   Let $\mathbf C = (C_1, \dots, C_k)$ be a product broadcast channel with $k \ge 1$ receivers, a common finite input alphabet $\mathcal X$ and finite output alphabets $\mathcal Y_i$. Suppose that for every randomized functionality $F = (f_i)_{i \in [k]}$ given by public polynomial-size target circuits $f_i(x; \rho_i)$ with independent coins there is an efficient one-way protocol $\Pi$ over $\mathbf C$ (Definition 4.2) whose correctness error $\varepsilon_{\mathrm{cor}}(\lambda)$ and whose security errors $\varepsilon_T(\lambda)$ for every coalition $T \subseteq \{S\} \cup [k]$ all satisfy
--   $$
--   \lim_{\lambda \to \infty} \varepsilon_{\mathrm{cor}}(\lambda) = 0, \qquad \lim_{\lambda \to \infty} \varepsilon_T(\lambda) = 0 .
--   $$
--   Then $\mathbf C$ satisfies noise preservation (Definition 4.5): every receiver $i$ has a bit $\beta_i : \mathcal X \times \mathcal Y_i \to \{0,1\}$ with nontrivial randomness at some input that every exact resampler of the joint observation preserves almost surely.
--
--   Together with the main theorem (Theorem 5.24) this shows that noise preservation is exactly the channel condition for one-way MPC of all randomized functionalities. The statement is information-theoretic and needs no assumption.
--
--   **Formalization Note** "Realization" is the base mission's encoding of Definition 4.2 (protocols, correctness and security errors, efficiency). Each error is a function of $\lambda$ that tends to $0$; it need not be negligible. One protocol serves all coalitions.
--
--   Differences from the source:
--   - encoding: every collection of independently randomized receiver functionalities → every Functionality k with IsPolyCircuit (public polynomial-size target circuits f_i(x; ρ_i), independent coins); reason: Definition 4.2 admits exactly these functionalities (p.18: 'each f_i is a public polynomial-size circuit')
--   - encoding: a realization with vanishing correctness and security errors → an efficient Protocol with CorrErr ε_cor and SecErr ε_T for every coalition (withS, J), each error tending to 0 as λ → ∞; reason: Definition 4.2 with the paper's conventions (§3, p.15: all algorithms PPT); 'vanishing' means tending to 0
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Theorem 6.2, p.40

import Mathlib
import Definitions.Def_NoisyOWMPC_SecErr
import Definitions.Def_NoisyOWMPC_NoisePreserving

namespace NoisyOWMPC.Supplement

open Filter Topology

/-- **Theorem 6.2 (Necessity of noise preservation)** (Ishai, Lu, Zafar, *Non-Interactive
Cryptography over Noisy Channels from Indistinguishability Obfuscation*, STOC 2027 submission
(manuscript sha256 3a9569fa…), Theorem 6.2, p.40): "Fix a product broadcast channel as in
Definition 4.2. If every collection of independently randomized receiver functionalities has a
realization with vanishing correctness and security errors, then the channels satisfy noise
preservation (Definition 4.5)."

Let `C = (C_1, …, C_k)` be a product broadcast channel with `k ≥ 1` receivers. Suppose that for
every functionality `F = (f_i)_i` given by public polynomial-size target circuits with independent
coins (Definition 4.2) there is an efficient protocol `Π` over `C` whose correctness error and
whose security error for every coalition `T` (every receiver set `J`, with or without the sender)
tend to `0` as `λ → ∞`. Then there are bits `β_i : X × Y_i → {0,1}` witnessing noise preservation
for every receiver `i`.

**Formalization Note** "Realization" is Definition 4.2 with the published `Protocol`, `CorrErr`,
`SecErr` and `IsEfficient` (polynomial lengths, a sender implementable within `2^{−λ}`,
polynomial-time receivers). "Vanishing" means each error function tends to `0`; it is not required
to be negligible. One protocol serves all coalitions, each with its own error function. The
statement is unconditional. -/
theorem theorem_6_2 {k : ℕ} (hk : 1 ≤ k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i))
    (hreal : ∀ F : Functionality k, F.IsPolyCircuit → ∃ P : Protocol k X Y F, P.IsEfficient ∧
      (∃ εcor : ℕ → ℝ, Tendsto εcor atTop (𝓝 0) ∧ P.CorrErr C εcor) ∧
      ∀ (withS : Bool) (J : Finset (Fin k)),
        ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ P.SecErr C withS J ε) :
    ∃ β : ∀ i, X → Y i → Bool, NoisePreserving C β := by sorry

end NoisyOWMPC.Supplement
