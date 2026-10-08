-- Prove2me | Theorems.Thm_InfoGen_Expected_theorem_1
-- name    : InfoGen.Expected.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:27:31.212736+00:00
-- url     : https://prove2.me/theorems/d3b0838b-4110-4ca1-bb41-2d66c220926b
-- title:
--   Theorem 1, p. 4 — if ℓ(w, Z) is σ-subgaussian for every w, then |gen(μ, P_{W|S})| ≤ √(2σ² I(S;W)/n)
-- statement:
--   This is the main theorem of Xu and Raginsky: the expected generalization error of a learning algorithm is bounded by the mutual information between its input and its output.
--
--   Let $\mathsf Z$ be an instance space, $\mathsf W$ a hypothesis space and $\ell:\mathsf W\times\mathsf Z\to\mathbb R_+$ a nonnegative, jointly measurable loss. Let $\mu$ be a probability measure on $\mathsf Z$, $n\ge1$, and $S=(Z_1,\dots,Z_n)\sim\mu^{\otimes n}$ an i.i.d. sample. A learning algorithm is a Markov kernel $P_{W|S}$ from $\mathsf Z^n$ to $\mathsf W$; the pair $(S,W)$ has law $P_{S,W}=\mu^{\otimes n}\otimes P_{W|S}$. With $L_\mu(w)=\mathbb E[\ell(w,Z)]$ and $L_S(w)=\frac1n\sum_{i=1}^n\ell(w,Z_i)$, the expected generalization error is $\mathrm{gen}(\mu,P_{W|S})=\mathbb E[L_\mu(W)-L_S(W)]$, and $I(S;W)=D(P_{S,W}\|P_S\otimes P_W)$ is the input–output mutual information.
--
--   Suppose that $\ell(w,Z)$ is $\sigma$-subgaussian under $\mu$ for all $w\in\mathsf W$, that is, $\log\mathbb E[e^{\lambda(\ell(w,Z)-L_\mu(w))}]\le\lambda^2\sigma^2/2$ for all $\lambda\in\mathbb R$, and that $I(S;W)<\infty$. Then
--   $$
--   \big|\mathrm{gen}(\mu,P_{W|S})\big|\le\sqrt{\frac{2\sigma^2}{n}\,I(S;W)} .
--   $$
--
--   The less the output hypothesis reveals about the training data, the smaller the expected gap between population and empirical risk. The bound places no restriction on the size of $\mathsf W$ and allows unbounded losses, provided they are subgaussian; a loss with values in $[a,b]$ is $(b-a)/2$-subgaussian for every $\mu$.
--
--   **Formalization Note** Subgaussianity is Mathlib's `HasSubgaussianMGF` of the centred loss with variance proxy $\sigma^2$ (the square of the paper's $\sigma$). The mutual information lives in $[0,\infty]$; the hypothesis $I(S;W)\neq\infty$ is added because Lean's conversion of $\infty$ to a real number gives $0$, which would turn the page's vacuous bound into a false one. Also added, as implicit on the page: $n\ge1$ (the bound divides by $n$) and joint measurability of $\ell$ (so that $L_\mu(W)$ and $L_S(W)$ are random variables). The nonnegativity of $\ell$ is the page's own assumption. The generalization error integrates the pointwise difference $L_\mu(W)-L_S(W)$; no integrability hypothesis is assumed.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Theorem 1, eq. (10), p. 4; proof p. 4 (first sentence) with Lemma 1 (p. 3) and App. A (p. 11)

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

open LearnStability.Characterization

/-- Theorem 1 (Xu & Raginsky, arXiv:1705.07809v2, p. 4, eq. (10)). Let `S` be an i.i.d. sample of
size `n ≥ 1` from `μ` and `W` the output of the learning algorithm `κ = P_{W|S}`. If `ℓ(w, Z)` is
`σ`-subgaussian under `μ` for every hypothesis `w` and `I(S; W) < ∞`, then
`|gen(μ, P_{W|S})| ≤ √((2σ²/n) I(S; W))`. -/
theorem theorem_1 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (hI : mutualInfo (sampleLaw μ n ⊗ₘ κ) ≠ ⊤) :
    |genError ℓ μ κ|
      ≤ Real.sqrt (2 * (σ : ℝ) ^ 2 / n * (mutualInfo (sampleLaw μ n ⊗ₘ κ)).toReal) := by sorry

end InfoGen.Expected
