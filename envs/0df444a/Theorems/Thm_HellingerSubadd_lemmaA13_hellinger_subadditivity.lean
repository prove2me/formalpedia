-- Prove2me | Theorems.Thm_HellingerSubadd_lemmaA13_hellinger_subadditivity
-- name    : HellingerSubadd.lemmaA13_hellinger_subadditivity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T02:56:07.616146+00:00
-- url     : https://prove2.me/theorems/7eeb124b-eb1d-47a7-ae2a-bd13a499f5fa
-- title:
--   Lemma A.13, eq. (97): subadditivity of squared Hellinger distance (corrected: $n\ge2$; at $n=1$ the right side is $0$)
-- statement:
--   Let $(\mathcal X_1,\mathcal F_1),\dots,(\mathcal X_n,\mathcal F_n)$ be measurable spaces, $\mathcal X^{(i)}=\prod_{t=1}^i\mathcal X_t$ and $\mathcal F^{(i)}=\bigotimes_{t=1}^i\mathcal F_t$. For each $i$ let $P^{(i)}(\cdot\mid\cdot)$ and $Q^{(i)}(\cdot\mid\cdot)$ be probability kernels from $(\mathcal X^{(i-1)},\mathcal F^{(i-1)})$ to $(\mathcal X_i,\mathcal F_i)$, and let $\mathbb P$ and $\mathbb Q$ be the laws of $X_1,\dots,X_n$ under $X_i\sim P^{(i)}(\cdot\mid X_{1:i-1})$ and $X_i\sim Q^{(i)}(\cdot\mid X_{1:i-1})$ respectively. Assume $n\ge2$ and that each $x_{1:i-1}\mapsto D^2_{\mathrm H}(P^{(i)}(\cdot\mid x_{1:i-1}),Q^{(i)}(\cdot\mid x_{1:i-1}))$ is measurable. Then
--
--   $$
--   D^2_{\mathrm H}(\mathbb P,\mathbb Q)\le10^2\log(n)\cdot\mathbb E_{\mathbb P}\Bigl[\sum_{i=1}^nD^2_{\mathrm H}\bigl(P^{(i)}(\cdot\mid X_{1:i-1}),Q^{(i)}(\cdot\mid X_{1:i-1})\bigr)\Bigr].
--   $$
--
--   Here $D^2_{\mathrm H}(\mu,\nu)=\int(\sqrt{d\mu}-\sqrt{d\nu})^2$ (no factor $1/2$) and $\log$ is the natural logarithm.
--
--   The lemma decomposes the Hellinger distance between two joint laws of an interaction history into the per-round conditional distances, up to a logarithmic factor and with no assumption on the likelihood ratios. It is the tool that turns per-round estimation error into a bound on the distance between the laws of whole interaction histories in the paper's upper bounds.
--
--   **Formalization Note** The spaces are indexed from $0$: coordinate $0$ is a fixed initial point $x_0$ of an arbitrary space $\mathcal X_0$ (the paper's one-point $\mathcal X^{(0)}$ is the case $\mathcal X_0=$ `PUnit`), and $P^{(i)}$, $Q^{(i)}$ are the kernels with index $i-1$. The laws are Mathlib's Ionescu-Tulcea partial trajectories.
--
--   Differences from the source:
--   - correction: (97) for every n → hypothesis 2 ≤ n; reason: false at n = 1: with X_1 = {0, 1}, P^(1) = δ_0, Q^(1) = δ_1 the left side is D²_H(δ_0, δ_1) = 2 and the right side 10² log 1 · E_P[2] = 0; the proof's last step 2(6 log 96n + 18/96n) ≤ 10² log n fails exactly at n = 1 and holds for n ≥ 2 (n = 0 is not a sequence of spaces)
--   - reading: X^(i) = ∏_{i=t}^i X_t (as printed) → ∏_{t=1}^i X_t (coordinates 1, …, i of the trajectory); reason: matches F^(i) = ⊗_{t=1}^i F_t in the same sentence; the printed index is a typo
--   - generalization: the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}), with X^(0) a one-point space → seqLaw κ n x₀ = Kernel.partialTraj κ 0 n x₀ on X 0 × ⋯ × X n, coordinate 0 a fixed initial point x₀ of an arbitrary space X 0; Markov kernels κ k given for every k : ℕ; reason: taking X 0 = PUnit gives the paper's setting; kernels with index ≥ n do not enter seqLaw κ n x₀, and any paper instance extends to all k (e.g. X k = PUnit with the unique kernel beyond n)
--   - encoding: P^(i)(· | x_{1:i−1}) for i = 1, …, n → κ (i − 1) applied to frestrictLe₂ of the trajectory (coordinates 0, …, i − 1); sum over k : Fin n; reason: 0-based indexing of Lean's ℕ-indexed Ionescu-Tulcea construction; the same kernels and the same sum
--   - encoding: E[Σ D²_H(P^(i), Q^(i))] with no measurability statement → ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y)); reason: the paper's expectation presupposes a measurable integrand; the hypothesis only excludes cases where that expectation is undefined (on general measurable spaces it is not automatic)
--   - encoding: real-valued divergences and expectations, real constants → values in ℝ≥0∞, expectations as lintegral, constants via ENNReal.ofReal; reason: every quantity is non-negative and finite where the paper uses it; the same instances
-- source:
--   Foster, Kakade, Qian & Rakhlin, The Statistical Complexity of Interactive Decision Making, arXiv:2112.13487v3, Lemma A.13, eq. (97), p. 73

import Mathlib
import Definitions.Def_HellingerSubadd_hellingerSq
import Definitions.Def_HellingerSubadd_seqLaw
import Definitions.Def_HellingerSubadd_condHellingerSum

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal

namespace HellingerSubadd

/-- **Lemma A.13, eq. (97) (subadditivity for squared Hellinger distance).**
Foster, Kakade, Qian & Rakhlin, *The Statistical Complexity of Interactive Decision Making*,
arXiv:2112.13487v3, Lemma A.13, eq. (97), p. 73: "Let (X_1, F_1), …, (X_n, F_n) be a sequence of
measurable spaces, and let X^(i) = ∏_{t=1}^i X_t and F^(i) = ⊗_{t=1}^i F_t. For each i, let
P^(i)(· | ·) and Q^(i)(· | ·) be probability kernels from (X^(i−1), F^(i−1)) to (X_i, F_i). Let P
and Q be the laws of X_1, …, X_n under X_i ∼ P^(i)(· | X_{1:i−1}) and X_i ∼ Q^(i)(· | X_{1:i−1})
respectively. Then it holds that
D²_H(P, Q) ≤ 10² log(n) · E_P[Σ_{i=1}^n D²_H(P^(i)(· | X_{1:i−1}), Q^(i)(· | X_{1:i−1}))]."

Here `X 1, …, X n` are the paper's spaces, `κ (i − 1)` is `P^(i)` and `η (i − 1)` is `Q^(i)`
(applied to coordinates `0, …, i − 1`), `P = seqLaw κ n x₀`, `Q = seqLaw η n x₀`.

**Formalization Note.**
* *Correction*: `2 ≤ n`. At `n = 1` the printed statement is false: `log 1 = 0`, while
  `P^(1) = δ_0`, `Q^(1) = δ_1` on `{0, 1}` give `D²_H(P, Q) = 2`. The proof's last step
  `2(6 log(96n) + 18/(96n)) ≤ 10² log(n)` fails exactly at `n = 1` and holds for all `n ≥ 2`.
* The index of the product `X^(i) = ∏_{i=t}^i X_t` (as printed) is read as `∏_{t=1}^i X_t`.
* Sequential laws are Mathlib's Ionescu-Tulcea `partialTraj` (`seqLaw`). Coordinate `0` is a
  common initial point `x₀`; the paper's `X^(0)` is a point (`X 0 = PUnit`). Kernels are given
  for every index `k : ℕ` and are Markov; those with `k ≥ n` do not enter, and any paper instance
  extends (e.g. by `X k = PUnit` beyond `n`).
* The conditional squared Hellinger distances `y ↦ D²_H(κ k y, η k y)` are assumed measurable for
  `k < n`: the paper's expectation presupposes it.
* Values in `ℝ≥0∞`, the expectation is a `lintegral`, the constant is
  `ENNReal.ofReal (10 ^ 2 * log n)` with the natural logarithm. -/
theorem lemmaA13_hellinger_subadditivity {X : ℕ → Type*} [∀ i, MeasurableSpace (X i)]
    (κ η : (k : ℕ) → Kernel (Π i : Iic k, X i) (X (k + 1)))
    [∀ k, IsMarkovKernel (κ k)] [∀ k, IsMarkovKernel (η k)]
    (x₀ : Π i : Iic 0, X i) (n : ℕ) (hn : 2 ≤ n)
    (hmeas : ∀ k < n, Measurable (fun y => hellingerSq (κ k y) (η k y))) :
    hellingerSq (seqLaw κ n x₀) (seqLaw η n x₀)
      ≤ ENNReal.ofReal (10 ^ 2 * Real.log n)
          * ∫⁻ x, condHellingerSum κ η n x ∂(seqLaw κ n x₀) := by sorry

end HellingerSubadd
