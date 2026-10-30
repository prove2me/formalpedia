-- Prove2me | Theorems.Thm_HellingerSubadd_kl_chain_rule_le
-- name    : HellingerSubadd.kl_chain_rule_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:50:04.468953+00:00
-- url     : https://prove2.me/theorems/b86f0161-8b16-4f00-898c-311832808f22
-- title:
--   Chain rule for KL divergence of sequential laws (corrected: "=" is "≤" on general measurable spaces)
-- statement:
--   Let $(\mathcal X_0,\mathcal F_0), (\mathcal X_1,\mathcal F_1), (\mathcal X_2,\mathcal F_2),\dots$ be measurable spaces and let $x_0 \in \mathcal X_0$ be a fixed initial point. For $k \ge 0$ let $P^{(k+1)}(\cdot \mid \cdot)$ and $Q^{(k+1)}(\cdot \mid \cdot)$ be probability kernels from $\mathcal X_0 \times \dots \times \mathcal X_k$ to $\mathcal X_{k+1}$. Write $\mathbb P$ and $\mathbb Q$ for the laws of $(x_0, X_1, \dots, X_n)$ when $X_i \sim P^{(i)}(\cdot \mid x_0, X_{1:i-1})$, respectively $X_i \sim Q^{(i)}(\cdot \mid x_0, X_{1:i-1})$, for $i = 1, \dots, n$. $D^2_{\mathrm H}$ is the squared Hellinger distance $\int(\sqrt{d\mu}-\sqrt{d\nu})^2$ (no factor $1/2$).
--
--   More generally, let $\kappa_k$ and $\eta_k$ ($k\ge0$) be any two families of probability kernels, with sequential laws $\mathbb P_\kappa$ and $\mathbb P_\eta$ started at the same point $x_0$. Assume that $y\mapsto D_{\mathrm{KL}}(\kappa_k(\cdot\mid y)\|\eta_k(\cdot\mid y))$ is measurable for every $k<n$. Then
--
--   $$
--   D_{\mathrm{KL}}(\mathbb P_\kappa\,\|\,\mathbb P_\eta)\le\mathbb E_{\mathbb P_\kappa}\Bigl[\sum_{i=1}^nD_{\mathrm{KL}}\bigl(\kappa_{i-1}(\cdot\mid X_{1:i-1})\,\big\|\,\eta_{i-1}(\cdot\mid X_{1:i-1})\bigr)\Bigr].
--   $$
--
--   The proof of Lemma A.13 applies it with $(\kappa,\eta)=(Q^{(\cdot)},P^{(\cdot)}_\lambda)$ in Term I and $(\kappa,\eta)=(P^{(\cdot)},P^{(\cdot)}_\lambda)$ in Term II.
--
--   Differences from the source:
--   - correction: D_KL(Q ∥ P_λ) = E_Q[Σ D_KL(Q^(i) ∥ P^(i)_λ)] (equality) → ≤; reason: on general measurable spaces the equality is false: X_1 = [0,1] (Borel, Lebesgue under both laws), X_2 = [0,1] with the countable–cocountable σ-algebra, P^(2)(·|x) = δ_x, Q^(2)(·|x) = the 0–1 measure of cocountable sets; the joint laws coincide (KL 0) while every conditional KL is ∞. The proof of Lemma A.13 uses only ≤
--   - generalization: the chain rule for the pairs (Q, P_λ) and (P, P_λ) → any two families of Markov kernels κ, η; reason: the mixture kernels are Markov for 0 ≤ λ ≤ 1, so κ := Q^(·) or P^(·), η := mixKernel recovers both uses
--   - generalization: the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}), with X^(0) a one-point space → seqLaw κ n x₀ = Kernel.partialTraj κ 0 n x₀ on X 0 × ⋯ × X n, coordinate 0 a fixed initial point x₀ of an arbitrary space X 0; Markov kernels κ k given for every k : ℕ; reason: taking X 0 = PUnit gives the paper's setting; kernels with index ≥ n do not enter seqLaw κ n x₀, and any paper instance extends to all k (e.g. X k = PUnit with the unique kernel beyond n)
--   - encoding: P^(i)(· | x_{1:i−1}) for i = 1, …, n → κ (i − 1) applied to frestrictLe₂ of the trajectory (coordinates 0, …, i − 1); sum over k : Fin n; reason: 0-based indexing of Lean's ℕ-indexed Ionescu-Tulcea construction; the same kernels and the same sum
--   - encoding: E[Σ D_KL(P^(i) ∥ Q^(i))] with no measurability statement → ∀ k < n, Measurable (fun y => klDiv (κ k y) (η k y)); reason: the paper's expectation presupposes a measurable integrand; the hypothesis only excludes cases where that expectation is undefined (on general measurable spaces it is not automatic)
--   - encoding: real-valued KL divergence and expectation → Mathlib's klDiv in ℝ≥0∞, expectation as lintegral; reason: klDiv equals the paper's KL for probability measures; non-negative integrand
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, proof of Lemma A.13, p. 73 (Term I, unnumbered display, "follows from the chain rule for KL divergence"); used again on p. 74 (Term II)

import Mathlib
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condKLSum

open MeasureTheory ProbabilityTheory InformationTheory Finset Preorder
open scoped ENNReal

namespace HellingerSubadd

/-- **Chain rule for KL divergence of sequential laws (inequality form).**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, proof of Lemma A.13, p. 73 (unnumbered): "D_KL(Q ∥ P_λ) =
E_Q[Σ_{i=1}^n D_KL(Q^(i)(· | X_{1:i−1}) ∥ P^(i)_λ(· | X_{1:i−1}))], where the right-hand expression
follows from the chain rule for KL divergence"; used again on p. 74 for `D_KL(P ∥ P_λ)`.

For two families of Markov kernels `κ, η`, with laws `P_κ = seqLaw κ n x₀` and
`P_η = seqLaw η n x₀`, whose conditional KL divergences `y ↦ D_KL(κ k y ∥ η k y)` are measurable
for `k < n`: `D_KL(P_κ ∥ P_η) ≤ E_{P_κ}[Σ_{k<n} D_KL(κ k (x_{0:k}) ∥ η k (x_{0:k}))]`.

**Formalization Note.** *Correction*: the paper writes "=". On general measurable spaces the
equality fails: with `X_1 = [0,1]` (Borel sets, Lebesgue measure under both laws), `X_2 = [0,1]`
with the countable–cocountable σ-algebra, `P^(2)(·|x) = δ_x` and `Q^(2)(·|x)` the 0–1 measure of
cocountable sets, the two joint laws coincide (joint KL `0`) while every conditional KL is `∞`.
The proof of Lemma A.13 uses only "≤", which is stated here. The paper applies the rule to
`(Q-kernels, mixture kernels)` and `(P-kernels, mixture kernels)`; it is stated for arbitrary
Markov kernel families. The measurability hypothesis is presupposed by the paper's expectation.
Sequential laws as in `seqLaw` (coordinate 0 is a common initial point). -/
theorem kl_chain_rule_le {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ)
    (hmeas : ∀ k < n, Measurable (fun y => klDiv (κ k y) (η k y))) :
    klDiv (seqLaw κ n x₀) (seqLaw η n x₀)
      ≤ ∫⁻ x, condKLSum κ η n x ∂(seqLaw κ n x₀) := by sorry

end HellingerSubadd
