-- Prove2me | Theorems.Thm_InterpOptStop_SAA_Supplement_theorem_EC_2
-- name    : InterpOptStop.SAA.Supplement.theorem_EC_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T22:53:22.12687+00:00
-- url     : https://prove2.me/theorems/4b6d72a2-c1a6-4ffb-af1d-915633f36224
-- title:
--   Theorem EC.2 (corrected: nonnegative grid levels) — one tree with value and depth guarantees
-- statement:
--   Under the continuous-cube Markov model and Assumptions EC.1–EC.4, with $T>0$, deterministic starting state $\bar x$, discount $\beta\in[0,1]$ and nonnegative constants $L,\lambda$, let $\epsilon>0$. There is one actual finite tree policy, allowed to split on the clock and the $n$ physical coordinates, with both
--   $$J^*(\bar x)-J^{\pi_{\rm tree}}(\bar x)\le\epsilon,\qquad\operatorname{depth}(\pi_{\rm tree})\le T+n\left\lceil\log_2\max\left\{1,\frac{2TL\lambda\sqrt n}{\epsilon}\right\}\right\rceil.$$
--   The ceiling counts nonnegative subdivision levels. For ratio at least one this is exactly the source coefficient and depth formula; it includes every positive $\epsilon$, and a zero coefficient gives depth at most $T$. This companion theorem relates approximation accuracy and the depth of the same concrete tree witness.
--
--   Differences from the source:
--   - encoding: continuous cube, Markov conditional laws, Euclidean Lipschitz g and C*, and the almost-sure transition bound (EC.31) → cube subtype, probability kernels with MarkovLaw, computed Bellman continuation, EuclideanLipschitz and DensityBound after the first period; reason: the history identity specifies the same conditional distribution and a kernel version of C*; compact-cube Lipschitz functions give bounded measurable rewards without an artificial G bound
--   - encoding: periods t=1,…,T and time coordinate t/T → k : Fin T and clockState k x=((k+1)/T,x), with the published J and finite Tree (n+1); reason: zero indexing preserves the discount β^(t−1); physical dimension in every bound remains n
--   - correction: depth at most T+n⌈log₂(2TLλ√n/ε)⌉ for every ε>0 → depth at most T+n⌈log₂(max{1,2TLλ√n/ε})⌉ with a natural level count; reason: ec29 constructs an integer partition with a nonnegative number of split levels; choose dyadic m=2^k to retain the exact coefficient for ratios ≥1; at T=n=L=λ=1 and ε=32 the literal signed bound is −3, impossible for any tree; the repaired bound covers large ε and zero coefficients without log 0
--   - correction: Theorem EC.2 quantifies a tree policy π̂ but prints J^π in the value gap → the value gap and depth bound use the same tree witness S and thresholds θ; reason: the proof on ec29 explicitly identifies π̂ as the approximating tree; the unbound π in the displayed value gap is a notation slip, with no change of domain or conclusion
-- source:
--   Ciocan & Mišić, Interpretable Optimal Stopping, arXiv:1812.07211v2, Theorem EC.2, p. ec29

import Mathlib
import Definitions.Def_InterpOptStop_SAA_Supplement_GridPolicy

open MeasureTheory ProbabilityTheory

namespace InterpOptStop.SAA.Supplement

theorem theorem_EC_2
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
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (S : Tree (n + 1)) (θ : Thresholds),
      cubeOptimalValue μ β g -
          treeValue (physicalLaw μ) β (extendReward g) S θ ≤ ε ∧
        S.depth ≤ T + n * gridLevels n T L lam ε := by sorry

end InterpOptStop.SAA.Supplement
