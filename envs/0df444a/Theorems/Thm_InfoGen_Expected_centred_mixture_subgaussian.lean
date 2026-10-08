-- Prove2me | Theorems.Thm_InfoGen_Expected_centred_mixture_subgaussian
-- name    : InfoGen.Expected.centred_mixture_subgaussian
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:26:25.885961+00:00
-- url     : https://prove2.me/theorems/14e9659c-39e7-4384-bfa5-67b3d98246d1
-- title:
--   §3.2, p. 4 (corrected) — L_s(w) − L_μ(w) is σ/√n-subgaussian with mean 0 under P_S ⊗ P_W
-- statement:
--   Let $\mathsf Z,\mathsf W,\ell,\mu,n,L_\mu,L_s$ be as in the learning setting: $\ell\ge0$ jointly measurable, $\mu$ a probability measure on $\mathsf Z$, $n\ge 1$, $L_\mu(w)=\int\ell(w,z)\,\mu(dz)$ and $L_s(w)=\frac1n\sum_{i=1}^n\ell(w,z_i)$. Let $P_{W|S}$ be a learning algorithm (a Markov kernel from $\mathsf Z^n$ to $\mathsf W$), let $P_{S,W}=\mu^{\otimes n}\otimes P_{W|S}$ be the joint law of the sample and the output, with marginals $P_S=\mu^{\otimes n}$ and $P_W$, and let $(\bar S,\bar W)\sim P_S\otimes P_W$ be independent copies.
--
--   Suppose that $\ell(w,Z)$ is $\sigma$-subgaussian under $\mu$ for every $w\in\mathsf W$. Then the centred empirical risk $f(s,w)=L_s(w)-L_\mu(w)$ satisfies
--   $$
--   \log\mathbb E\Big[e^{\lambda f(\bar S,\bar W)}\Big]\le\frac{\lambda^2\sigma^2}{2n}\quad\text{for all }\lambda\in\mathbb R,\qquad\text{and}\qquad \mathbb E\big[f(\bar S,\bar W)\big]=0 .
--   $$
--   In words, $f(\bar S,\bar W)$ is $\sigma/\sqrt n$-subgaussian with mean zero under $P_S\otimes P_W$.
--
--   This is the second half of the step from Lemma 1 to Theorem 1: under the product of the marginals, $f(\bar S,\bar W)$ is a mixture over $\bar W$ of mean-zero $\sigma/\sqrt n$-subgaussian variables, so Lemma 1 applies to it with $\sigma/\sqrt n$ in place of $\sigma$, and $\mathbb E[f(S,W)]=-\mathrm{gen}(\mu,P_{W|S})$.
--
--   **Formalization Note** The page states that the *uncentred* $f(\bar S,\bar W)=L_{\bar S}(\bar W)$ is $\sigma/\sqrt n$-subgaussian; that is false in general (take $\ell(w,z)=w$ with $\bar W$ uniform on $\{0,1\}$: every $\ell(w,Z)$ is constant, hence $0$-subgaussian, but $L_{\bar S}(\bar W)=\bar W$ is not $0$-subgaussian). The statement here is the centred version, which is what the proof of Theorem 1 uses. Subgaussianity is Mathlib's `HasSubgaussianMGF` with variance proxy $\sigma^2/n$; since the variable is already shown to have mean $0$, no further centring is needed. The product of the marginals is written `J.fst.prod J.snd` for the joint law `J = sampleLaw μ n ⊗ₘ κ`, the same measure used in the definition of $I(S;W)$. Joint measurability of $\ell$ and $n\ge 1$ are added.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, §3.2, p. 4, first sentence ("hence f(S̄, W̄) is σ/√n-subgaussian"), corrected to the centred f(s, w) = L_s(w) − L_μ(w); with eq. (9), p. 3

import Mathlib
import Definitions.Def_InfoGen_Expected_Setting

open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal NNReal

namespace InfoGen.Expected

open LearnStability.Characterization

/-- §3.2, p. 4, second clause, corrected (Xu & Raginsky, arXiv:1705.07809v2). Let
`J = μ^{⊗n} ⊗ P_{W|S}` be the joint law of `(S, W)` and `J_S ⊗ J_W` the law of independent copies
`(S̄, W̄)`. If `ℓ(w, Z)` is `σ`-subgaussian under `μ` for every `w`, then the centred function
`f(s, w) = L_s(w) − L_μ(w)` is `σ/√n`-subgaussian under `J_S ⊗ J_W` (variance proxy `σ²/n`), and
its mean there is `0`. The page states this for the uncentred `L_{S̄}(W̄)`, which is false in
general; the centred version is what Lemma 1 needs. -/
theorem centred_mixture_subgaussian {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (κ : Kernel (Fin n → Z) W) [IsMarkovKernel κ]
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ) :
    let J := sampleLaw μ n ⊗ₘ κ
    HasSubgaussianMGF (fun p => empRisk ℓ p.1 p.2 - risk ℓ μ p.2) (σ ^ 2 / n)
        (J.fst.prod J.snd) ∧
      ∫ p, (empRisk ℓ p.1 p.2 - risk ℓ μ p.2) ∂(J.fst.prod J.snd) = 0 := by sorry

end InfoGen.Expected
