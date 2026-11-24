-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_lemma_EC_7
-- name    : InterpOptStop.SAA.Supplement.lemma_EC_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:51:08.935815+00:00
-- url     : https://prove2.me/theorems/8836b1d5-7596-4625-bbb7-43e53b27f56f
-- title:
--   Lemma EC.7 — all successive intermediate-policy gaps
-- statement:
--   Let $T>0$, $\bar x\in[0,1]^n$, and let the process start deterministically at $\bar x$. Assume $0\le\beta\le1$ and Assumptions EC.1–EC.4: the full continuous cube, the Markov property, Euclidean $L$-Lipschitz rewards and Bellman continuation values, and the almost-sure transition-density bound $\lambda$, with $L,\lambda\ge0$. For any positive integer $m$, construct the specified survival-conditioned grid policy $\hat\pi$. Let $\tilde\pi^i$ follow it for the first $i$ periods and the Bellman-optimal policy thereafter. Then, for every $i=0,\ldots,T-1$,
--   $$J^{\tilde\pi^i}(\bar x)-J^{\tilde\pi^{i+1}}(\bar x)\le\frac{2L\lambda\sqrt n}{m}.$$
--   Both the initial pair and the final pair ending at $\tilde\pi^T=\hat\pi$ are present. This is the successive-policy estimate underlying Theorem EC.1.
--
--   Differences from the source:
--   - encoding: continuous cube, Markov conditional laws, Euclidean Lipschitz g and C*, and the almost-sure transition bound (EC.31) → cube subtype, probability kernels with MarkovLaw, computed Bellman continuation, EuclideanLipschitz and DensityBound after the first period; reason: the history identity specifies the same conditional distribution and a kernel version of C*; compact-cube Lipschitz functions give bounded measurable rewards without an artificial G bound
--   - reading: integer subdivision m and the unique cube h(x) in (EC.32)–(EC.34) → positive natural m, shared faces owned by the lower cell, with 0 included in the first cell; survival conditioning, strict stop, and zero conditional means on null events; reason: m≤0 does not define a subdivision; face ownership completes the source partition and agrees with the published ≤-left splits; null and tie conventions are explicit on ec25
--   - encoding: intermediate policies follow an optimal policy after the first i periods → intermediatePolicy uses the computed Bellman-optimal policy, with i=0 through T and adjacent gaps for every i<T; reason: the Bellman recursion supplies a definite optimal feedback policy; the ec25 endpoint π̃ᵀ supplies the final adjacent pair; i=0 is retained and does not use the false initial density estimate
--   - encoding: periods t=1,…,T and time coordinate t/T → k : Fin T and clockState k x=((k+1)/T,x), with the published J and finite Tree (n+1); reason: zero indexing preserves the discount β^(t−1); physical dimension in every bound remains n
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Lemma EC.7, p. ec27

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

theorem lemma_EC_7
    {n T : ℕ} (hT : 0 < T)
    (μ : Measure (Fin T → Cube n)) [IsProbabilityMeasure μ]
    (xbar : Cube n) (hstart : ∀ᵐ p ∂μ, p ⟨0, hT⟩ = xbar)
    (β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (g : Fin T → Cube n → ℝ)
    (K : Fin T → Kernel (Cube n) (Cube n)) (hK : ∀ k : Fin T, k.val + 1 < T → IsMarkovKernel (K k))
    (hMarkov : MarkovLaw μ K)
    (L lam : ℝ) (hL : 0 ≤ L) (hlam : 0 ≤ lam)
    (hg : ∀ k, EuclideanLipschitz L (g k))
    (hC : ∀ k, EuclideanLipschitz L (continuation β g K k))
    (hdensity : DensityBound μ K lam)
    (m : ℕ) (hm : 0 < m) :
    ∀ i : ℕ, i < T →
      cubeValue μ β g (intermediatePolicy μ β g K m i) -
        cubeValue μ β g (intermediatePolicy μ β g K m (i + 1)) ≤
          2 * L * lam * Real.sqrt n / m := by sorry

end InterpOptStop.SAA.Supplement
