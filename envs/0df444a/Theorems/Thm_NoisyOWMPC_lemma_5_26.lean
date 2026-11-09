-- Prove2me | Theorems.Thm_NoisyOWMPC_lemma_5_26
-- name    : NoisyOWMPC.lemma_5_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T07:59:02.691241+00:00
-- url     : https://prove2.me/theorems/eb68db14-de48-44f7-b5e6-3443ad60780a
-- title:
--   Lemma 5.26 — correctness and honest outputs
-- statement:
--   In the setting of Theorem 5.25, consider Construction 5.23 with an iO scheme, a Fig. 6 program generator and a pad size that every program fits. There is a negligible $\nu$ such that for every $\lambda$, input $x$ and set $I\subseteq[k]$ of receivers, the probability that some $i\in I$ has $y_i\ne y^*_i$ is at most
--   $$|I|\alpha+q_I(N\eta+\alpha_{\mathrm{sel}})+\nu(\lambda),$$
--   where $y^*_i$ is the honest output (5.14). In particular, correctness holds with error $k\alpha+q(N\eta+\alpha_{\mathrm{sel}})+\nu(\lambda)$.
--
--   Differences from the source:
--   - generalization: recoverable access and release tests and a recoverable selector (Theorem 5.25's setting) → only the properties the proof uses: completeness α (trivial access test when k = 1), unbiasedness η, honest acceptance α_sel and balance, with probability laws; reason: recoverable tests and selectors have these properties, so the lemma specializes to the paper's
--   - generalization: the paper's padded program → every polynomial-time Fig. 6 generator and every pad size the program fits; reason: the paper's implementation is one such generator
--   - reading: negl(λ) → one negligible ν, uniform over x and I; reason: the paper's negligible terms are sampler-precision terms independent of x
--   - reading: 'polynomial M = M(λ)', 'even N = N(λ) ≥ λ polynomial in λ', 'public polynomially bounded parameters' (Definition 4.2) → public polynomial parameters (PolyParam): polynomially bounded and computed from 1^λ in polynomial time; reason: every polynomial in λ qualifies; the parties and simulators are polynomial-time algorithms and must compute the public parameters
--   - encoding: for k = 1 'the trivial test that always accepts' (Definition 5.2) → channel-input length 0, one state with weight 1 encoded by the empty string, every query accepted (TestHalf.IsTrivial); reason: the trivial test has one state; its encoding carries no information
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Lemma 5.26, p.32 ((5.14), p.31)

import Mathlib
import Definitions.Def_NoisyOWMPC_construction
import Definitions.Def_NoisyOWMPC_SecErr

namespace NoisyOWMPC

/-- **Lemma 5.26 (Correctness and honest outputs)** (Ishai, Lu, Zafar, STOC 2027 submission
(manuscript sha256 3a9569fa…), Lemma 5.26, p.32, in the setting of Theorem 5.25, p.31): "For every
`I ⊆ [k]`, the probability that some `i ∈ I` has `y_i ≠ y*_i` is at most
`|I|α + q_I(Nη + α_sel) + negl(λ)`. In particular, correctness holds with the bound of Theorem
5.25." Here `y*_i` is the honest output (5.14), p.31, and the correctness bound is
`kα + q(Nη + α_sel) + negl(λ)`.

The protocol is Construction 5.23 for a product broadcast channel with nonconstant marginals,
access tests complete with error `α` (the trivial test with `α = 0` when `k = 1`), release tests
unbiased with error `η`, and a selector with honest acceptance `α_sel` and balance, an iO scheme,
a generator of Fig. 6 and a pad size `s` that every generated program fits.

**Formalization Note** Only the properties the lemma uses are assumed of the tests and the selector
(completeness, unbiasedness, honest acceptance, balance, and that the samplers' laws are probability
distributions); recoverable tests (Definitions 5.2–5.4) have them. -/
theorem lemma_5_26 {k : ℕ} (hk : 1 ≤ k) {X : Type} [Fintype X] {Y : Fin k → Type}
    [∀ i, Fintype (Y i)] (C : ∀ i, DMC X (Y i)) (hC : ∀ i, Nonconstant (C i))
    (H : Halves k X Y) (F : Functionality k) (hF : F.IsPolyCircuit) (α η αsel : ℕ → ℝ)
    (hacc : (1 < k → ∀ i, (H.acc i).IsDist ∧ (H.acc i).Complete C α) ∧
      (¬ 1 < k → (∀ i, (H.acc i).IsTrivial) ∧ ∀ lam, α lam = 0))
    (hrel : ∀ i, (H.rel i).IsDist ∧ (H.rel i).Unbiased C η)
    (hsel : H.sel.IsDist ∧ H.sel.HonestAccept αsel ∧ H.sel.Balanced)
    (O : IOScheme) (hO : O.IsIO) (gen : ProgGen H F) (hgen : IsFig6Gen H F gen) (s : ℕ → ℕ)
    (hs : ∀ lam x c, (gen lam x c).base.gates.length ≤ s lam) :
    ∃ ν : ℕ → ℝ, Negligible ν ∧
      (∀ lam (x : Fin (F.lx lam) → Bool) (I : Finset (Fin k)),
        wprob ((construction H F O gen s).realW C lam x) (fun ω => ∃ i ∈ I,
            (construction H F O gen s).out lam x ω i ≠ some (ystar H F O gen s lam x ω i)) ≤
          (I.card : ℝ) * α lam +
            (F.qOf I lam : ℝ) * ((H.N lam : ℝ) * η lam + αsel lam) + ν lam) ∧
      (construction H F O gen s).CorrErr C (fun lam => (k : ℝ) * α lam +
        (F.qOf Finset.univ lam : ℝ) * ((H.N lam : ℝ) * η lam + αsel lam) + ν lam) := by sorry

end NoisyOWMPC
