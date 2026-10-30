-- Prove2me | Theorems.Thm_HellingerSubadd_combined_bound
-- name    : HellingerSubadd.combined_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:54:40.501683+00:00
-- url     : https://prove2.me/theorems/b22cc9f6-94a8-4df7-9271-5e123549a858
-- title:
--   Combined bound: $D^2_{\mathrm H}(\mathbb P,\mathbb Q)\le(6\log(1/\lambda)+18\lambda)\,\mathbb E_{\mathbb Q}[\cdots]+48\lambda n\,D^2_{\mathrm H}(\mathbb P,\mathbb Q)$
-- statement:
--   Let $(\mathcal X_0,\mathcal F_0), (\mathcal X_1,\mathcal F_1), (\mathcal X_2,\mathcal F_2),\dots$ be measurable spaces and let $x_0 \in \mathcal X_0$ be a fixed initial point. For $k \ge 0$ let $P^{(k+1)}(\cdot \mid \cdot)$ and $Q^{(k+1)}(\cdot \mid \cdot)$ be probability kernels from $\mathcal X_0 \times \dots \times \mathcal X_k$ to $\mathcal X_{k+1}$. Write $\mathbb P$ and $\mathbb Q$ for the laws of $(x_0, X_1, \dots, X_n)$ when $X_i \sim P^{(i)}(\cdot \mid x_0, X_{1:i-1})$, respectively $X_i \sim Q^{(i)}(\cdot \mid x_0, X_{1:i-1})$, for $i = 1, \dots, n$. $D^2_{\mathrm H}$ is the squared Hellinger distance $\int(\sqrt{d\mu}-\sqrt{d\nu})^2$ (no factor $1/2$). Let $\lambda\in(0,e^{-1})$ and assume that $y\mapsto D^2_{\mathrm H}(P^{(k+1)}(\cdot\mid y),Q^{(k+1)}(\cdot\mid y))$ is measurable for every $k<n$. Then
--
--   $$
--   D^2_{\mathrm H}(\mathbb P,\mathbb Q)\le\bigl(6\log(1/\lambda)+18\lambda\bigr)\,\mathbb E_{\mathbb Q}\Bigl[\sum_{i=1}^nD^2_{\mathrm H}\bigl(P^{(i)}(\cdot\mid X_{1:i-1}),Q^{(i)}(\cdot\mid X_{1:i-1})\bigr)\Bigr]+48\lambda n\,D^2_{\mathrm H}(\mathbb P,\mathbb Q).
--   $$
--
--   It combines the bounds on Terms I and II; choosing $\lambda$ small makes the coefficient of $D^2_{\mathrm H}(\mathbb P,\mathbb Q)$ on the right less than one.
--
--   Differences from the source:
--   - generalization: the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}), with X^(0) a one-point space → seqLaw κ n x₀ = Kernel.partialTraj κ 0 n x₀ on X 0 × ⋯ × X n, coordinate 0 a fixed initial point x₀ of an arbitrary space X 0; Markov kernels κ k given for every k : ℕ; reason: taking X 0 = PUnit gives the paper's setting; kernels with index ≥ n do not enter seqLaw κ n x₀, and any paper instance extends to all k (e.g. X k = PUnit with the unique kernel beyond n)
--   - encoding: P^(i)(· | x_{1:i−1}) for i = 1, …, n → κ (i − 1) applied to frestrictLe₂ of the trajectory (coordinates 0, …, i − 1); sum over k : Fin n; reason: 0-based indexing of Lean's ℕ-indexed Ionescu-Tulcea construction; the same kernels and the same sum
--   - encoding: E[Σ D²_H(P^(i), Q^(i))] with no measurability statement → ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y)); reason: the paper's expectation presupposes a measurable integrand; the hypothesis only excludes cases where that expectation is undefined (on general measurable spaces it is not automatic)
--   - encoding: real-valued divergences and expectations, real constants → values in ℝ≥0∞, expectations as lintegral, constants via ENNReal.ofReal; reason: every quantity is non-negative and finite where the paper uses it; the same instances
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 74 ("Completing the proof", first display)

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condHellingerSum

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Combined bound on `D²_H(P, Q)` for a parameter `λ ∈ (0, e⁻¹)`.**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 74 ("Completing the proof"): "Combining our bounds on
terms I and II and using the elementary fact that (x + y)² ≤ 2(x² + y²), we have
D²_H(P, Q) ≤ (6 log(1/λ) + 18λ) E_Q[Σ_{i=1}^n D²_H(P^(i)(· | X_{1:i−1}), Q^(i)(· | X_{1:i−1}))]
+ 48λnD²_H(P, Q)."

Here `κ` are the kernels `P^(i)`, `η` the kernels `Q^(i)`, `P = seqLaw κ n x₀`, `Q = seqLaw η n x₀`.

**Formalization Note.** The conditional squared Hellinger distances `y ↦ D²_H(κ k y, η k y)` are
assumed measurable for `k < n` (the paper's expectation presupposes it). The summand order
`(P^(i), Q^(i))` is the printed one. Values in `ℝ≥0∞`, real factors through `ENNReal.ofReal`. -/
theorem combined_bound {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam < Real.exp (-1))
    (hmeas : ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y))) :
    hellingerSq (seqLaw κ n x₀) (seqLaw η n x₀)
      ≤ ENNReal.ofReal (6 * Real.log (1 / lam) + 18 * lam)
            * ∫⁻ x, condHellingerSum κ η n x ∂(seqLaw η n x₀)
          + ENNReal.ofReal (48 * lam * n) * hellingerSq (seqLaw κ n x₀) (seqLaw η n x₀) := by sorry

end HellingerSubadd
