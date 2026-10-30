-- Prove2me | Theorems.Thm_HellingerSubadd_termII_after_lemmaA11
-- name    : HellingerSubadd.termII_after_lemmaA11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:00.814067+00:00
-- url     : https://prove2.me/theorems/917efc3f-e8cc-42a8-a0f5-8ddfa6d0cc71
-- title:
--   Term II after Lemma A.11: bound $9\lambda\,\mathbb E_{\mathbb Q}[\sum_i D^2_{\mathrm H}(P^{(i)},Q^{(i)})]+24\lambda n\,D^2_{\mathrm H}(\mathbb P,\mathbb Q)$
-- statement:
--   Let $(\mathcal X_0,\mathcal F_0), (\mathcal X_1,\mathcal F_1), (\mathcal X_2,\mathcal F_2),\dots$ be measurable spaces and let $x_0 \in \mathcal X_0$ be a fixed initial point. For $k \ge 0$ let $P^{(k+1)}(\cdot \mid \cdot)$ and $Q^{(k+1)}(\cdot \mid \cdot)$ be probability kernels from $\mathcal X_0 \times \dots \times \mathcal X_k$ to $\mathcal X_{k+1}$. Write $\mathbb P$ and $\mathbb Q$ for the laws of $(x_0, X_1, \dots, X_n)$ when $X_i \sim P^{(i)}(\cdot \mid x_0, X_{1:i-1})$, respectively $X_i \sim Q^{(i)}(\cdot \mid x_0, X_{1:i-1})$, for $i = 1, \dots, n$. $D^2_{\mathrm H}$ is the squared Hellinger distance $\int(\sqrt{d\mu}-\sqrt{d\nu})^2$ (no factor $1/2$). For $\lambda \in (0, e^{-1})$ let $P^{(i)}_\lambda = (1-\lambda)P^{(i)} + \lambda Q^{(i)}$ and let $\mathbb P_\lambda$ be the law of the process driven by the kernels $P^{(i)}_\lambda$. Assume that $y\mapsto D^2_{\mathrm H}(P^{(k+1)}(\cdot\mid y),Q^{(k+1)}(\cdot\mid y))$ is measurable for every $k<n$, and write $S=\sum_{i=1}^nD^2_{\mathrm H}(P^{(i)}(\cdot\mid X_{1:i-1}),Q^{(i)}(\cdot\mid X_{1:i-1}))$. Then both
--
--   $$
--   3\lambda\cdot\mathbb E_{\mathbb P}[S]\le9\lambda\cdot\mathbb E_{\mathbb Q}[S]+24\lambda n\cdot D^2_{\mathrm H}(\mathbb P,\mathbb Q)
--   \qquad\text{and}\qquad
--   D^2_{\mathrm H}(\mathbb P_\lambda,\mathbb P)\le9\lambda\cdot\mathbb E_{\mathbb Q}[S]+24\lambda n\cdot D^2_{\mathrm H}(\mathbb P,\mathbb Q).
--   $$
--
--   This is the bound on Term II that enters the final combination in the proof of Lemma A.13: since $S\le2n$, Lemma A.11 replaces the expectation under $\mathbb P$ by one under $\mathbb Q$ at the cost of a multiple of $D^2_{\mathrm H}(\mathbb P,\mathbb Q)$.
--
--   Differences from the source:
--   - reading: "Lemma A.11 gives the following upper bound: 9λ·E_Q[…] + 24λn·D²_H(P, Q)" (the bounded quantity is not named) → the conjunction: the bound for 3λ·E_P[…] (what Lemma A.11 is applied to) and for D²_H(P_λ, P) (what it is used for); reason: the sentence admits both readings; the conjunction is not weaker than either
--   - generalization: the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}), with X^(0) a one-point space → seqLaw κ n x₀ = Kernel.partialTraj κ 0 n x₀ on X 0 × ⋯ × X n, coordinate 0 a fixed initial point x₀ of an arbitrary space X 0; Markov kernels κ k given for every k : ℕ; reason: taking X 0 = PUnit gives the paper's setting; kernels with index ≥ n do not enter seqLaw κ n x₀, and any paper instance extends to all k (e.g. X k = PUnit with the unique kernel beyond n)
--   - encoding: P^(i)(· | x_{1:i−1}) for i = 1, …, n → κ (i − 1) applied to frestrictLe₂ of the trajectory (coordinates 0, …, i − 1); sum over k : Fin n; reason: 0-based indexing of Lean's ℕ-indexed Ionescu-Tulcea construction; the same kernels and the same sum
--   - encoding: E[Σ D²_H(P^(i), Q^(i))] with no measurability statement → ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y)); reason: the paper's expectation presupposes a measurable integrand; the hypothesis only excludes cases where that expectation is undefined (on general measurable spaces it is not automatic)
--   - encoding: real-valued divergences and expectations, real constants → values in ℝ≥0∞, expectations as lintegral, constants via ENNReal.ofReal; reason: every quantity is non-negative and finite where the paper uses it; the same instances
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (Term II, display after "Lemma A.11 gives the following upper bound")

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condHellingerSum
import Definitions.Def_HellingerSubadd_mixKernel

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Term II after Lemma A.11: the bound `9λ · E_Q[Σ D²_H(P^(i), Q^(i))] + 24λn · D²_H(P, Q)`.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 74: "Since the sum inside the expectation on the
right-hand side is bounded by 2n with probability 1, Lemma A.11 gives the following upper bound:
9λ · E_Q[Σ_{i=1}^n D²_H(P^(i)(· | X_{1:i−1}), Q^(i)(· | X_{1:i−1}))] + 24λn · D²_H(P, Q)."

The bound is stated both for the right-hand side `3λ · E_P[Σ D²_H(P^(i), Q^(i))]` of the preceding
display (the quantity Lemma A.11 is applied to) and for `D²_H(P_λ, P)` (the quantity it is used to
bound in "Completing the proof"). Here `κ` are the kernels `P^(i)`, `η` the kernels `Q^(i)`,
`P = seqLaw κ n x₀`, `Q = seqLaw η n x₀`, `P_λ = seqLaw (mixKernel κ η lam) n x₀`, `λ ∈ (0, e⁻¹)`.

**Formalization Note.** The paper's sentence does not say which of the two quantities the
printed expression bounds; both are asserted (a conjunction), which is not weaker than either
reading. The conditional squared Hellinger distances are assumed measurable for `k < n` (the
paper's expectations presuppose it). Values in `ℝ≥0∞`, real factors through `ENNReal.ofReal`. -/
theorem termII_after_lemmaA11 {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < Real.exp (-1))
    (hmeas : ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y))) :
    ENNReal.ofReal (3 * lam) * ∫⁻ x, condHellingerSum κ η n x ∂(seqLaw κ n x₀)
        ≤ ENNReal.ofReal (9 * lam) * ∫⁻ x, condHellingerSum κ η n x ∂(seqLaw η n x₀)
          + ENNReal.ofReal (24 * lam * n) * hellingerSq (seqLaw κ n x₀) (seqLaw η n x₀)
      ∧ hellingerSq (seqLaw (mixKernel κ η lam) n x₀) (seqLaw κ n x₀)
        ≤ ENNReal.ofReal (9 * lam) * ∫⁻ x, condHellingerSum κ η n x ∂(seqLaw η n x₀)
          + ENNReal.ofReal (24 * lam * n) * hellingerSq (seqLaw κ n x₀) (seqLaw η n x₀) := by sorry

end HellingerSubadd
