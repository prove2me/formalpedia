-- Prove2me | Theorems.Thm_GamblersFallacy_Supplement_theorem_4
-- name    : GamblersFallacy.Supplement.theorem_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:15:17.874034+00:00
-- url     : https://prove2.me/theorems/cf83e58a-84a3-5dbe-96d8-28771c589063
-- title:
--   Theorem 4 (corrected: truncated-cycle holding term) — the expected CPUGS of the SBS policy under discrete demand
-- statement:
--   Let the cycles $(Z_t,Y_t)$, $t\ge1$, be i.i.d. with the joint law $P(Y=k,Z=j)=p_{kj}$ on $[K]\times[J]$, the process starting right after a nonzero demand at time $0$. Let $h,b\ge0$ be the holding and shortage costs, let $S_j\ge0$ for $j\in[J]$ be the SBS levels, and let $n\ge1$. Write $C_{kj}=\sum_{\ell=1}^{j-1}hS_\ell+h(S_j-k)^++b(k-S_j)^+$. Then the expected CPUGS over $n$ periods is
--   $$
--   \mathbb E[C(\pi^{sd})]=\sum_{j\in[J]}\sum_{k\in[K]}\tilde p_{kj}(n)\,\frac{C_{kj}}{k}\;+\;\mathbb E\Bigg[\chi(X_n=0)\,\frac{h\sum_{\ell=1}^{\,n-(Z_1+\dots+Z_\tau)}S_\ell}{Y_1+\dots+Y_\tau+1}\Bigg],
--   $$
--   with $\tilde p_{kj}(n)$ the biased estimate of the paper.
--
--   The finite-horizon CPUGS is thus a single-cycle cost under the biased weights $\tilde p_{kj}(n)$, plus the holding cost of a truncated last cycle. The SBS levels can then be optimized by the linear program (4) with that extra term included.
--
--   **Formalization Note** The cycles live on an arbitrary probability space. $(Z_t,Y_t)_{t\ge1}$ are independent, each with the cycle law $\sum p_{kj}\delta_{(j,k)}$. All expectations are lower Lebesgue integrals in $[0,\infty]$, so no integrability hypothesis is needed.
--
--   Differences from the source:
--   - correction: $\mathbb E[C(\pi^{sd})]=\sum_j\sum_k\tilde p_{kj}(n)C_{kj}/k$ (3) → (3) plus $\mathbb E[\chi(X_n=0)\,h\sum_{\ell\le n-(Z_1+\dots+Z_\tau)}S_\ell/(Y_1+\dots+Y_\tau+1)]$; reason: a truncated last cycle costs holding by the definition of $C_{\mathrm{tail}}$ on p.20, and no term of $\tilde p_{kj}(n)$ carries it. At $n=1$, $J=2$, $K=1$, $p_{11}=p_{12}=1/2$, $h=b=1$, $S_1=S_2=1$ the expected CPUGS is $1/2$ and the printed right side is $0$. The corrected identity held in exact arithmetic on 25 random instances ($J,K\le3$, $n\le4$), and the printed one failed on 6 of them
--   - generalization: SBS levels with $S_0=0$, $S_{j-1}\le S_j$, $S_j\ge0$ → only $S_j\ge0$ for $j\in[J]$; reason: the identity does not use monotonicity, $S_0$ never enters the costs, and for monotone levels it is the source's statement
--   - encoding: unit costs $h,b$ → hypotheses $h,b\ge0$, with expectations as lower Lebesgue integrals in $[0,\infty]$; reason: costs are nonnegative in the source; with them every integrand is nonnegative and the $[0,\infty]$ expectations are the source's
--   - encoding: i.i.d. cycles with joint law $p_{kj}$, "starting from an initial state after a nonzero demand" → an arbitrary probability space with $(Z_t,Y_t)_{t\ge1}$ independent, each with law $\sum p_{kj}\delta_{(j,k)}$, the initial demand at time $0$ not counted; reason: the model of §4.2.1–4.2.2
--   - encoding: an $n$-period horizon → $n\ge1$; reason: $\tau=\max\{t:\sum_{s\le t}Z_s\le n-1\}$ needs $n\ge1$
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 4, (3), p.21 (proof EC.2.4, pp.ec5–ec6); CPUGS and C_tail, p.20; SBS policy, p.19

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_CPUGS
import Definitions.Def_GamblersFallacy_Supplement_DiscreteSBS

namespace GamblersFallacy.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 4 (corrected: truncated-cycle holding term) — the expected CPUGS of the SBS policy
under discrete demand.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 4, p.21 (proof EC.2.4,
pp.ec5–ec6): "Starting from an initial state after a nonzero demand, over a finite horizon of n
periods, the expected CPUGS can be expressed by the cycle cost with the biased estimates p̃_kj(n),
E[C(π^sd)] = Σ_{j∈[J]} Σ_{k∈[K]} p̃_kj(n) (Σ_{ℓ=1}^{j−1} hS_ℓ + h(S_j − k)⁺ + b(k − S_j)⁺)/k." (3)

Let the cycles `(Z_t, Y_t)`, `t ≥ 1`, be i.i.d. with the joint law `p_kj` of size and
inter-arrival time, let `h, b ≥ 0` and `S_j ≥ 0` for `j ∈ [J]`, and `n ≥ 1`. Then
`E[CPUGS] = Σ_{j∈[J]} Σ_{k∈[K]} p̃_kj(n) C_kj / k + E[truncated-cycle holding term]`.

**Correction.** The printed (3) has no second summand. A truncated last cycle (no demand at `n`)
costs `h Σ_{ℓ ≤ n − (Z₁+⋯+Z_τ)} S_ℓ`, which `C_tail` includes by the definition on p.20 but which
no `p̃_kj(n)` term carries. Counterexample to (3): `n = 1`, `J = 2`, `K = 1`,
`p₁₁ = p₁₂ = 1/2`, `h = b = 1`, `S₁ = S₂ = 1` gives CPUGS `1/2` against `0` on the right.

**Formalization Note.** The demand process is given on an arbitrary probability space; `(Z t, Y t)`
for `t ≥ 1` are independent with law `D.cycleLaw`; expectations are lower Lebesgue integrals
(`ℝ≥0∞`), so no integrability hypothesis is needed. The monotonicity `S_{j−1} ≤ S_j` of the SBS
levels is not needed and not assumed. -/
theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (D : JointDemandLaw) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hY : ∀ t, Measurable (Y t))
    (hind : iIndepFun (fun t ω => (Z (t + 1) ω, Y (t + 1) ω)) P)
    (hlaw : ∀ t, 1 ≤ t → P.map (fun ω => (Z t ω, Y t ω)) = D.cycleLaw)
    (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (S : ℕ → ℝ) (hS : ∀ l ∈ Finset.Icc 1 D.J, 0 ≤ S l)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, ENNReal.ofReal (cpugs h b S Z Y n ω) ∂P =
      (∑ j ∈ Finset.Icc 1 D.J, ∑ k ∈ Finset.Icc 1 D.K,
        biasedJointWeight P Z Y n k j * ENNReal.ofReal (sbsCycleCost h b S k j / k)) +
      ∫⁻ ω, ENNReal.ofReal (truncatedHolding h S Z Y n ω) ∂P := by sorry

end GamblersFallacy.Supplement
