-- Prove2me | Theorems.Thm_FoundationsRL_DECLower_kl_chain_rule_eq_of_standardBorel
-- name    : FoundationsRL.DECLower.kl_chain_rule_eq_of_standardBorel
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:16:43.211991+00:00
-- url     : https://prove2.me/theorems/64dddb80-9736-4ca1-be84-89e5f4e40aca
-- title:
--   Lemma 22 — chain rule for KL divergence, equality (corrected: spaces standard Borel)
-- statement:
--   Let $(\mathcal X_k,\mathcal F_k)_{k\ge 0}$ be measurable spaces such that $\mathcal X_1,\mathcal X_2,\dots$ are standard Borel, let $x_0\in\mathcal X_0$, and for each $k$ let $\kappa_k,\eta_k$ be probability kernels from $\mathcal X_0\times\dots\times\mathcal X_k$ to $\mathcal X_{k+1}$. Let $P$ and $Q$ be the laws of $(x_0,X_1,\dots,X_n)$ under $X_i\sim\kappa_{i-1}(\cdot\mid x_0,X_{1:i-1})$ and $X_i\sim\eta_{i-1}(\cdot\mid x_0,X_{1:i-1})$. Then
--
--   $$
--   D_{\mathrm{KL}}(P\,\|\,Q)=\mathbb E_P\left[\sum_{i=1}^n D_{\mathrm{KL}}\bigl(\kappa_{i-1}(\cdot\mid x_0,X_{1:i-1})\,\big\|\,\eta_{i-1}(\cdot\mid x_0,X_{1:i-1})\bigr)\right].
--   $$
--
--   This is Lemma 22 with the equality, on the spaces where it holds; it covers every concrete decision-making setting with Polish decision, reward and observation spaces.
--
--   Differences from the source:
--   - correction: equality on arbitrary measurable spaces $\mathcal X_1,\dots,\mathcal X_n$ → equality when $\mathcal X_1,\mathcal X_2,\dots$ are standard Borel; reason: the printed equality is false in general (the countable–cocountable counterexample of the inequality milestone satisfies every assumption of the lemma)
--   - reading: $\mathcal X^i=\prod_{i=t}\mathcal X_t$ → $\prod_{t=1}^i\mathcal X_t$; reason: index typo in the PDF
--   - generalization: kernels from $\mathcal X^{i-1}$ with $\mathcal X^0$ a point → kernels that may also depend on a fixed initial point $x_0$ of an arbitrary $\mathcal X_0$; reason: a one-point $\mathcal X_0$ is exactly the notes' case
--   - encoding: $n$ spaces and kernels → families indexed by all of $\mathbb N$, only the first $n$ kernels enter; standard Borel assumed for every $\mathcal X_{k+1}$; KL divergence in $[0,\infty]$; reason: Lean convention; spaces beyond $n$ are free parameters that do not enter
-- source:
--   Foster & Rakhlin, Foundations of Reinforcement Learning and Interactive Decision Making, arXiv:2312.16730v1, Lemma 22, (6.35), p. 107

import Mathlib
import Definitions.Def_FoundationsRL_DECLower_seqLaw
import Definitions.Def_FoundationsRL_DECLower_condKLSum

open MeasureTheory ProbabilityTheory InformationTheory Finset Preorder
open scoped ENNReal

namespace FoundationsRL.DECLower

/-- **Lemma 22 (Chain rule for KL divergence), equality on standard Borel spaces.**
Foster & Rakhlin, *Foundations of Reinforcement Learning and Interactive Decision Making*,
arXiv:2312.16730v1, Lemma 22, (6.35), p. 107.

If every `X_i` (`i ≥ 1`) is a standard Borel space, then for two families of probability kernels
`κ, η` with sequential laws `P = seqLaw κ n x₀`, `Q = seqLaw η n x₀`:
`D_KL(P ∥ Q) = E_P[Σ_{i=1}^n D_KL(P_i(· | X_{1:i−1}) ∥ Q_i(· | X_{1:i−1}))]`.

**Formalization Note.** *Correction*: the notes state the equality for arbitrary measurable spaces,
where it is false (counterexample in `kl_chain_rule_le`, with a countable–cocountable `X_2`); it
holds when the spaces `X_1, …, X_n` are standard Borel. The initial coordinate `X 0` is
arbitrary (the paper's empty product is `X 0 = PUnit`). No measurability hypothesis is needed:
for a countably generated target, `y ↦ D_KL(κ k y ∥ η k y)` is measurable. -/
theorem kl_chain_rule_eq_of_standardBorel {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    [∀ i, StandardBorelSpace (X (i + 1))]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) :
    klDiv (seqLaw κ n x₀) (seqLaw η n x₀)
      = ∫⁻ x, condKLSum κ η n x ∂(seqLaw κ n x₀) := by sorry

end FoundationsRL.DECLower
