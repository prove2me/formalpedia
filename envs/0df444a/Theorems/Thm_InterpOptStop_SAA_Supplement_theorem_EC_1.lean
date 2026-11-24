-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_theorem_EC_1
-- name    : InterpOptStop.SAA.Supplement.theorem_EC_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:52:10.563819+00:00
-- url     : https://prove2.me/theorems/f3d86813-0ce6-407f-94eb-0395e2bd8a20
-- title:
--   Theorem EC.1 — value bound for the specified survival-conditioned policy
-- statement:
--   In the full continuous-cube stopping model, let $T>0$, deterministic start $\bar x$, discount $\beta\in[0,1]$, Euclidean Lipschitz constant $L\ge0$ and transition-density bound $\lambda\ge0$. Assume the Markov property and all of Assumptions EC.1–EC.4. For every positive integer $m$, the particular policy $\hat\pi$ computed by (EC.32)–(EC.34), with conditioning on survival and the current cell, satisfies
--   $$J^*(\bar x)-J^{\hat\pi}(\bar x)\le\frac{2T\lambda L\sqrt n}{m}.$$
--   This bounds the source-defined policy, rather than merely asserting the existence of a policy with this error. It uses the unrestricted stopping optimum and keeps the initial deterministic state, including $T=1$. Lipschitz rewards on the compact cube ensure bounded integrable payoffs without a supplied reward bound $G$. The compact-stopping-region and smooth-marginal assumptions of Theorem 2 are not required.
--
--   Differences from the source:
--   - encoding: continuous cube, Markov conditional laws, Euclidean Lipschitz g and C*, and the almost-sure transition bound (EC.31) → cube subtype, probability kernels with MarkovLaw, computed Bellman continuation, EuclideanLipschitz and DensityBound after the first period; reason: the history identity specifies the same conditional distribution and a kernel version of C*; compact-cube Lipschitz functions give bounded measurable rewards without an artificial G bound
--   - reading: integer subdivision m and the unique cube h(x) in (EC.32)–(EC.34) → positive natural m, shared faces owned by the lower cell, with 0 included in the first cell; survival conditioning, strict stop, and zero conditional means on null events; reason: m≤0 does not define a subdivision; face ownership completes the source partition and agrees with the published ≤-left splits; null and tie conventions are explicit on ec25
--   - encoding: periods t=1,…,T and time coordinate t/T → k : Fin T and clockState k x=((k+1)/T,x), with the published J and finite Tree (n+1); reason: zero indexing preserves the discount β^(t−1); physical dimension in every bound remains n
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Theorem EC.1, p. ec25

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

theorem theorem_EC_1
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
    cubeOptimalValue μ β g - cubeValue μ β g (gridPolicy μ β g K m) ≤
      2 * T * lam * L * Real.sqrt n / m := by sorry

end InterpOptStop.SAA.Supplement
