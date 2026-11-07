-- Prove2me | Theorems.Thm_OnlineShadow_LogRate_theorem_1_2
-- name    : OnlineShadow.LogRate.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:57.110236+00:00
-- url     : https://prove2.me/theorems/dd7015d4-3e0b-4923-b0ba-81ce2a8fc58e
-- title:
--   Theorem 1.2 — online shadow tomography with $O(\sqrt K\log(m+K)/\varepsilon^2)$ copies, $K=\Theta(\log d/\varepsilon^2)$
-- statement:
--   In **online shadow tomography** a learner holds $n$ copies of an unknown state $\rho$ on $\mathbb C^d$. An adversary chooses observables $0\preceq A^{(1)},\dots,A^{(m)}\preceq1$ one at a time, each as a function of the transcript of earlier observables and answers; after receiving $A^{(t)}$ the learner, which may measure its copies adaptively, must answer $\widehat\mu^{(t)}$ with $|\widehat\mu^{(t)}-\mathrm{Tr}(A^{(t)}\rho)|\le\varepsilon$.
--
--   **Theorem 1.2.** There are absolute constants $C_1,C_2>0$ such that for every dimension $d$, every number of rounds $m\ge1$ and every $\varepsilon>0$, with
--   $$K=\frac{C_1\log d}{\varepsilon^2},$$
--   there are a number of copies
--   $$n\le\frac{C_2\sqrt K\,\log(m+K)}{\varepsilon^2}$$
--   and an online protocol on $n$ copies such that, for every density matrix $\rho$ on $\mathbb C^d$ and every adaptive adversary, all $m$ answers are within $\varepsilon$ of $\mathrm{Tr}(A^{(t)}\rho)$ simultaneously with probability at least $9/10$.
--
--   This matches the best known classical rate $O(\log(m)\sqrt{\log d}/\varepsilon^3)$ for adaptive data analysis up to the $\log K$ term.
--
--   **Formalization Note** The protocol answers by one complete quantum instrument per round, adaptive in the history and blind to $\rho$, and is chosen before $\rho$ and the adversary; the adversary is a deterministic function of the transcript. $\log$ is the natural logarithm.
--
--   Differences from the source:
--   - encoding: n = O(√K log(m + K)/ε²) for K = Θ(log(d)/ε²) → ∃ absolute C₁, C₂ > 0 before d, m, ε; K := C₁ log d/ε² (a real number); n ≤ C₂ √K log(m + K)/ε²; reason: the bound increases in K, so a constant multiple of log d/ε² is the Θ for an upper bound; another log base rescales C₁, C₂ (paper.md R1)
--   - encoding: "there is a protocol" → an OnlineProtocol: per round one complete instrument with a finite outcome set on (ℂ^d)^{⊗n}, adaptive in past observables and outcomes, no ancilla; chosen before ρ and the adversary; reason: adaptive measurements within a round compose into one instrument and coins are Kraus operators √p·1, so Algorithm 1 fits; no ancilla only makes the claim harder (paper.md R2)
--   - encoding: adversary selects A⁽ᵗ⁺¹⁾ based on the transcript → a deterministic function of the transcript, quantified after ρ; reason: a randomized adversary is a mixture of deterministic ones (paper.md R3)
--   - reading: correctly answers m … observables to error ε with probability at least 9/10 → all m answers satisfy |μ̂ − Tr(Aρ)| ≤ ε simultaneously with probability ≥ 9/10; reason: Definition 1.1's ≤ ε; "correctly answers m observables" is the joint event (paper.md R4)
--   - encoding: m rounds, every d, error parameter ε > 0 → m ≥ 1, every d, every ε > 0; reason: at m = 0 nothing is asked and log(0 + K) may be negative (paper.md R5)
--   - encoding: Tr(·) of the product → the real part .trace.re; reason: every such trace is of a Hermitian operator or of a product of two Hermitian operators, so it is real and the real part is its value
-- source:
--   Chen, O'Donnell, Pelecanos, Wright, Online Shadow Tomography Matching the Classical Bounds, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), Theorem 1.2, p. 3 (restated p. 10)

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_OnlineShadow_LogRate_successProb

open scoped ComplexOrder

namespace OnlineShadow.LogRate

/-- **Theorem 1.2** (Chen, O'Donnell, Pelecanos, Wright, *Online Shadow Tomography Matching the Classical Bounds*, STOC 2027 submission (manuscript of November 2, 2026, sha256 90993723…dc3a9), p.3; restated p.10). There is a protocol for online shadow tomography of
`d`-dimensional states that, using `n = O(√K log(m + K)/ε²)` copies of the unknown state with
`K = Θ(log(d)/ε²)`, correctly answers `m` adaptively chosen observables to error `ε` with probability
at least `9/10`: there are absolute constants `C₁, C₂ > 0` such that for every `d`, every `m ≥ 1` and
every `ε > 0`, with `K = C₁ log d/ε²`, some `n ≤ C₂ √K log(m + K)/ε²` and some online protocol on `n`
copies satisfy: for every density matrix `ρ` on `ℂ^d` and every adaptive adversary, all `m` answers are
within `ε` of `Tr(A⁽ᵗ⁾ρ)` simultaneously with probability at least `9/10`.

**Formalization Note** (paper.md R1–R5) `O` and `Θ` are absolute constants `C₁, C₂` chosen before
`d, m, ε`; `K` is the real number `C₁ log d/ε²` (natural log); the bound on `n` increases in `K`, so
`∃ C₁` is "`K = Θ(log d/ε²)`" for an upper bound. The protocol (`OnlineProtocol`: one complete
instrument with finite outcome set per round, adaptive in the history, blind to `ρ`) is chosen before
`ρ` and the adversary; the adversary is a deterministic function of the transcript. `m ≥ 1`: at
`m = 0` nothing is asked and `log(K)` may be negative. -/
theorem theorem_1_2 :
    ∃ C₁ C₂ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧
      ∀ (d m : ℕ) (ε : ℝ), 1 ≤ m → 0 < ε →
        let K : ℝ := C₁ * Real.log d / ε ^ 2
        ∃ n : ℕ, (n : ℝ) ≤ C₂ * Real.sqrt K * Real.log (m + K) / ε ^ 2 ∧
          ∃ (O : Type) (_ : Fintype O) (P : OnlineProtocol d n O),
            ∀ ρ : Matrix (Fin d) (Fin d) ℂ, WildeQIT.IsDensityOperator ρ →
              ∀ adv : Adversary d, 9 / 10 ≤ successProb m P ρ adv ε := by sorry

end OnlineShadow.LogRate
