-- Prove2me | Theorems.Thm_HellingerSubadd_termI_bound
-- name    : HellingerSubadd.termI_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:51:45.896379+00:00
-- url     : https://prove2.me/theorems/99586c8c-5c37-4258-b7b7-9d43163005cf
-- title:
--   Term I: $D^2_{\mathrm H}(\mathbb P_\lambda,\mathbb Q)\le 3\log(1/\lambda)\,\mathbb E_{\mathbb Q}[\sum_i D^2_{\mathrm H}(Q^{(i)},P^{(i)})]$
-- statement:
--   Let $(\mathcal X_0,\mathcal F_0), (\mathcal X_1,\mathcal F_1), (\mathcal X_2,\mathcal F_2),\dots$ be measurable spaces and let $x_0 \in \mathcal X_0$ be a fixed initial point. For $k \ge 0$ let $P^{(k+1)}(\cdot \mid \cdot)$ and $Q^{(k+1)}(\cdot \mid \cdot)$ be probability kernels from $\mathcal X_0 \times \dots \times \mathcal X_k$ to $\mathcal X_{k+1}$. Write $\mathbb P$ and $\mathbb Q$ for the laws of $(x_0, X_1, \dots, X_n)$ when $X_i \sim P^{(i)}(\cdot \mid x_0, X_{1:i-1})$, respectively $X_i \sim Q^{(i)}(\cdot \mid x_0, X_{1:i-1})$, for $i = 1, \dots, n$. $D^2_{\mathrm H}$ is the squared Hellinger distance $\int(\sqrt{d\mu}-\sqrt{d\nu})^2$ (no factor $1/2$). For $\lambda \in (0, e^{-1})$ let $P^{(i)}_\lambda = (1-\lambda)P^{(i)} + \lambda Q^{(i)}$ and let $\mathbb P_\lambda$ be the law of the process driven by the kernels $P^{(i)}_\lambda$. Assume that $y\mapsto D^2_{\mathrm H}(Q^{(k+1)}(\cdot\mid y),P^{(k+1)}(\cdot\mid y))$ is measurable for every $k<n$. Then
--
--   $$
--   D^2_{\mathrm H}(\mathbb P_\lambda,\mathbb Q)\le3\log(1/\lambda)\cdot\mathbb E_{\mathbb Q}\Bigl[\sum_{i=1}^nD^2_{\mathrm H}\bigl(Q^{(i)}(\cdot\mid X_{1:i-1}),P^{(i)}(\cdot\mid X_{1:i-1})\bigr)\Bigr].
--   $$
--
--   This is the bound on the first of the two terms into which the triangle inequality splits $D_{\mathrm H}(\mathbb P,\mathbb Q)$ in the proof of Lemma A.13.
--
--   Differences from the source:
--   - generalization: the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}), with X^(0) a one-point space → seqLaw κ n x₀ = Kernel.partialTraj κ 0 n x₀ on X 0 × ⋯ × X n, coordinate 0 a fixed initial point x₀ of an arbitrary space X 0; Markov kernels κ k given for every k : ℕ; reason: taking X 0 = PUnit gives the paper's setting; kernels with index ≥ n do not enter seqLaw κ n x₀, and any paper instance extends to all k (e.g. X k = PUnit with the unique kernel beyond n)
--   - encoding: P^(i)(· | x_{1:i−1}) for i = 1, …, n → κ (i − 1) applied to frestrictLe₂ of the trajectory (coordinates 0, …, i − 1); sum over k : Fin n; reason: 0-based indexing of Lean's ℕ-indexed Ionescu-Tulcea construction; the same kernels and the same sum
--   - encoding: E[Σ D²_H(Q^(i), P^(i))] with no measurability statement → ∀ k < n, Measurable (fun y => hellingerSq (η k y) (κ k y)); reason: the paper's expectation presupposes a measurable integrand; the hypothesis only excludes cases where that expectation is undefined (on general measurable spaces it is not automatic)
--   - encoding: real-valued divergences and expectations, real constants → values in ℝ≥0∞, expectations as lintegral, constants via ENNReal.ofReal; reason: every quantity is non-negative and finite where the paper uses it; the same instances
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (Term I, display after "We conclude that")

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condHellingerSum
import Definitions.Def_HellingerSubadd_mixKernel

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Term I bound: `D²_H(P_λ, Q) ≤ 3 log(1/λ) · E_Q[Σ D²_H(Q^(i), P^(i))]`.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 74 (display after "We conclude that"):
"D²_H(P_λ, Q) ≤ 3 log(1/λ) · E_Q[Σ_{i=1}^n D²_H(Q^(i)(· | X_{1:i−1}), P^(i)(· | X_{1:i−1}))]".

Here `κ` are the kernels `P^(i)`, `η` the kernels `Q^(i)`, `P_λ = seqLaw (mixKernel κ η lam) n x₀`,
`Q = seqLaw η n x₀`, and `λ ∈ (0, e⁻¹)` is the proof's parameter (p. 73).

**Formalization Note.** The conditional squared Hellinger distances `y ↦ D²_H(η k y, κ k y)` are
assumed measurable for `k < n`; the paper's expectation presupposes it. The summand order
`(Q^(i), P^(i))` is the printed one. Sequential laws as in `seqLaw` (coordinate 0 a common initial
point; the paper's case is `X 0 = PUnit`). Values in `ℝ≥0∞`, the real factor through
`ENNReal.ofReal`. -/
theorem termI_bound {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < Real.exp (-1))
    (hmeas : ∀ k < n, Measurable (fun y => hellingerSq (η k y) (κ k y))) :
    hellingerSq (seqLaw (mixKernel κ η lam) n x₀) (seqLaw η n x₀)
      ≤ ENNReal.ofReal (3 * Real.log (1 / lam))
          * ∫⁻ x, condHellingerSum η κ n x ∂(seqLaw η n x₀) := by sorry

end HellingerSubadd
