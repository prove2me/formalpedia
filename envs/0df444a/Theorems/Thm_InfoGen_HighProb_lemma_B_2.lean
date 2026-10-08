-- Prove2me | Theorems.Thm_InfoGen_HighProb_lemma_B_2
-- name    : InfoGen.HighProb.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:00.669464+00:00
-- url     : https://prove2.me/theorems/51a21ed5-b6c7-457f-95be-f4ce6e303b1c
-- title:
--   Lemma B.2, p. 11 — if I(Λ_W(S₁),…,Λ_W(S_m);W,T,R) ≤ ε and ℓ(w,Z) is σ-subgaussian, then E[R(L_{S_T}(W) − L_μ(W))] ≤ √(2σ²ε/n)
-- statement:
--   Let $\mathsf W$ be a countable hypothesis space, $\mu$ a probability measure on the instance space $\mathsf Z$, and $\ell : \mathsf W\times\mathsf Z\to\mathbb R_+$ a jointly measurable loss such that, for every $w\in\mathsf W$, $\ell(w,Z)$ with $Z\sim\mu$ is $\sigma$-subgaussian: $\log \mathbb E[e^{\lambda(\ell(w,Z) - L_\mu(w))}] \le \lambda^2\sigma^2/2$ for all $\lambda\in\mathbb R$. Let $n \ge 1$, $m \ge 1$, and let $S^m = (S_1,\dots,S_m)$ be $m$ independent datasets, $S_t\sim\mu^{\otimes n}$.
--
--   Let $P_{W,T,R|S^m}$ be any algorithm (Markov kernel) that takes $S^m$ as input and outputs a triple $(W, T, R) \in \mathsf W\times[m]\times\{\pm1\}$. If, for some $\varepsilon\ge 0$,
--   $$I\big(\Lambda_{\mathsf W}(S_1),\dots,\Lambda_{\mathsf W}(S_m);\, W, T, R\big) \le \varepsilon,$$
--   then
--   $$\mathbb E\big[R\,(L_{S_T}(W) - L_\mu(W))\big] \le \sqrt{\frac{2\sigma^2\varepsilon}{n}} .$$
--   The expectation is under the joint law of $(S^m, W, T, R)$.
--
--   The bound does not depend on $m$. Applied to the monitor's output in the proof of Theorem 3, it bounds the expected maximal deviation over $m$ parallel runs.
--
--   **Formalization Note.** $[m]$ is `Fin m`, and $R\in\{\pm1\}$ is a Boolean read through `sgn` (`true` $\mapsto 1$, `false` $\mapsto -1$). $\sigma$-subgaussianity is Mathlib's `HasSubgaussianMGF` of the centred loss with variance proxy $\sigma^2$. $\mathsf W$ is countable with measurable singletons (the paper's claim for uncountable $\mathsf W$ fails, see Theorem 3); joint measurability of $\ell$ and $n\ge1$, $m\ge1$, $\varepsilon\ge0$ are added. The expectation is a real (Bochner) integral; under the hypotheses the integrand is integrable, so it is the paper's expectation. The paper's proof asserts that $f((\Lambda_{\mathsf W}(s_t))_t,(w,t,r)) = r L_{s_t}(w)$ is $\sigma/\sqrt n$-subgaussian under the product of the marginals, which is false in general (its mean varies with $w$); the lemma itself is true, as the centred function $r(L_{s_t}(w) - L_\mu(w))$ shows.
-- source:
--   Xu & Raginsky, arXiv:1705.07809v2, Lemma B.2, p. 11 (proof via Lemma 1, p. 3)

import Mathlib
import Definitions.Def_InfoGen_HighProb_Setting

open MeasureTheory ProbabilityTheory InformationTheory LearnStability.Characterization
open scoped ENNReal NNReal

namespace InfoGen.HighProb

theorem lemma_B_2 {Z W : Type*} [MeasurableSpace Z] [MeasurableSpace W]
    [Countable W] [MeasurableSingletonClass W]
    (μ : Measure Z) [IsProbabilityMeasure μ] (n : ℕ) (hn : 0 < n)
    (ℓ : W → Z → ℝ) (hℓ : Measurable (Function.uncurry ℓ)) (hℓ0 : ∀ w z, 0 ≤ ℓ w z)
    (σ : ℝ≥0) (hσ : ∀ w, HasSubgaussianMGF (fun z => ℓ w z - risk ℓ μ w) (σ ^ 2) μ)
    (m : ℕ) (hm : 0 < m)
    (η : Kernel (Fin m → Fin n → Z) (W × Fin m × Bool)) [IsMarkovKernel η]
    (ε : ℝ) (hε0 : 0 ≤ ε)
    (hε : InfoGen.Expected.mutualInfo (((Measure.pi (fun _ : Fin m => sampleLaw μ n)) ⊗ₘ η).map
        (fun p => ((fun t => empRiskVec ℓ (p.1 t)), p.2))) ≤ ENNReal.ofReal ε) :
    ∫ p, sgn p.2.2.2 * (empRisk ℓ (p.1 p.2.2.1) p.2.1 - risk ℓ μ p.2.1)
        ∂((Measure.pi (fun _ : Fin m => sampleLaw μ n)) ⊗ₘ η) ≤
      Real.sqrt (2 * (σ : ℝ) ^ 2 * ε / n) := by sorry

end InfoGen.HighProb
