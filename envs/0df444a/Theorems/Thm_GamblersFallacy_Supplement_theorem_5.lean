-- Prove2me | Theorems.Thm_GamblersFallacy_Supplement_theorem_5
-- name    : GamblersFallacy.Supplement.theorem_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:16:39.128982+00:00
-- url     : https://prove2.me/theorems/ad728fa7-d190-447e-b1c0-905b6c83cc63
-- title:
--   Theorem 5 (corrected: last-cycle term of $\tilde p_j(n,\theta)$, truncated-cycle holding term) — the expected CPUGS of the SBS policy under continuous demand
-- statement:
--   Let the cycles $(Z_t,Y_t)$, $t\ge1$, be i.i.d., with $P(Z=j)=p_j$ on $[J]$. Given $Z=j$, let the demand size $Y$ have the density $f_j$ on $(0,\infty)$, and let the process start right after a nonzero demand at time $0$. Let $h,b\ge0$, let $S_j\ge0$ for $j\in[J]$, and let $n\ge1$. Write $C_{\theta j}=\sum_{\ell=1}^{j-1}hS_\ell+h(S_j-\theta)^++b(\theta-S_j)^+$. Then the expected CPUGS over $n$ periods is
--   $$
--   \mathbb E[C(\pi^{sd})]=\sum_{j\in[J]}\int_0^\infty\tilde p_j(n,\theta)\,\frac{C_{\theta j}}{\theta}\,d\theta\;+\;\mathbb E\Bigg[\chi(X_n=0)\,\frac{h\sum_{\ell=1}^{\,n-(Z_1+\dots+Z_\tau)}S_\ell}{Y_1+\dots+Y_\tau+1}\Bigg].
--   $$
--   Here $\tilde p_j(n,\theta)$ is the biased density with the corrected last-cycle term $\chi(\sum_{s\le\tau}Z_s=n-j)\,\chi(Z_{\tau+1}=j)\,\theta/(\sum_{s\in[\tau]}Y_s+\max\{1,\theta\})$.
--
--   This is the continuous counterpart of Theorem 4. The finite-horizon CPUGS is a single-cycle cost integrated against the biased densities $\tilde p_j(n,\theta)$, plus the holding cost of a truncated last cycle, which gives the optimization problem (6) with that term included.
--
--   **Formalization Note** The cycles live on an arbitrary probability space, and $(Z_t,Y_t)_{t\ge1}$ are independent with the cycle law. All expectations and the $\theta$-integral are lower Lebesgue integrals in $[0,\infty]$, so no integrability hypothesis is added. The factor $C_{\theta j}/\theta$ need not be integrable near $0$, and both sides may be $+\infty$.
--
--   Differences from the source:
--   - correction: the last-cycle term of $\tilde p_j(n,\theta)$, $\chi(\sum_{s\le\tau}Z_s=n-j)/((\sum_{s\in[\tau]}Y_s+\theta)/\theta)$ → $\chi(\sum_{s\le\tau}Z_s=n-j)\,\chi(Z_{\tau+1}=j)\,\theta/(\sum_{s\in[\tau]}Y_s+\max\{1,\theta\})$; reason: the last-cycle cost enters only if the next demand arrives at $n$, and the CPUGS denominator counts it as $\max\{1,X_n\}$. At $n=1$, $J=2$, $p=(1/2,1/2)$, $f_1=f_2$ uniform on $(1,2)$, $h=0$, $b=1$, $S_1=S_2=0$ the expected CPUGS is $1/2$ and the printed right side is $1$. A density with mass on $(0,1)$ also separates $\theta$ from $\max\{1,\theta\}$
--   - correction: $\mathbb E[C(\pi^{sd})]=\sum_j\int\tilde p_j(n,\theta)C_{\theta j}/\theta\,d\theta$ → plus $\mathbb E[\chi(X_n=0)\,h\sum_{\ell\le n-(Z_1+\dots+Z_\tau)}S_\ell/(Y_1+\dots+Y_\tau+1)]$; reason: as in Theorem 4, a truncated last cycle costs holding by the definition of $C_{\mathrm{tail}}$ on p.20. At $n=1$, $J=2$, $p=(1/2,1/2)$, $f_1=f_2$ uniform on $(1,2)$, $h=1$, $b=0$, $S_1=S_2=1$ the expected CPUGS is $1/2$, while the right side without the added term is $0$. A Monte Carlo check of the corrected identity at $n=3$ agreed to sampling error
--   - generalization: SBS levels with $S_0=0$, $S_{j-1}\le S_j$, $S_j\ge0$ → only $S_j\ge0$ for $j\in[J]$; reason: the identity does not use monotonicity, $S_0$ never enters the costs, and for monotone levels it is the source's statement
--   - encoding: unit costs $h,b$ and $\int_\theta\cdots d\theta$ → hypotheses $h,b\ge0$, expectations and the integral over $\theta\in(0,\infty)$ as lower Lebesgue integrals in $[0,\infty]$; reason: costs are nonnegative in the source and the densities live on $(0,\infty)$; with them every integrand is nonnegative and the $[0,\infty]$ quantities are the source's, with no integrability condition added
--   - encoding: i.i.d. cycles with densities $f_j$ conditional on $Z=j$, "starting from an initial state after nonzero demand" → an arbitrary probability space with $(Z_t,Y_t)_{t\ge1}$ independent, each with law $\sum_jp_j(f_j\,d\theta)$ on $\{j\}\times\mathbb R$; reason: the model of §4.2.3
--   - encoding: an $n$-period horizon → $n\ge1$; reason: $\tau=\max\{t:\sum_{s\le t}Z_s\le n-1\}$ needs $n\ge1$
-- source:
--   Bi–He–Teo, Taming the Long Tail, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 5, p.22 (proof EC.2.5, p.ec6); density f_j, §4.2.3, p.21; CPUGS and C_tail, p.20; SBS policy, p.19

import Mathlib
import Definitions.Def_GamblersFallacy_Supplement_RenewalLaw
import Definitions.Def_GamblersFallacy_Supplement_CPUGS
import Definitions.Def_GamblersFallacy_Supplement_ContinuousSBS

namespace GamblersFallacy.Supplement

open MeasureTheory ProbabilityTheory

/-- **Theorem 5 (corrected: tail term of `p̃_j(n, θ)` and truncated-cycle holding term) — the
expected CPUGS of the SBS policy under continuous demand.**
S. Bi, L. He, C.-P. Teo, *Taming the Long Tail: The Gambler's Fallacy in Intermittent Demand
Management*, MSOM (2023), doi:10.1287/msom.2023.1217, Theorem 5, p.22 (proof EC.2.5, p.ec6):
"Starting from an initial state after nonzero demand, over a finite horizon of n periods, the
expected CPUGS can be expressed by the cycle cost with the biased estimates p̃_j(n, θ):
E[C(π^sd)] = Σ_{j∈[J]} ∫_θ p̃_j(n, θ) (Σ_{ℓ=1}^{j−1} hS_ℓ + h(S_j − θ)⁺ + b(θ − S_j)⁺)/θ dθ."

Let the cycles `(Z_t, Y_t)`, `t ≥ 1`, be i.i.d.: `P(Z = j) = p_j` and, given `Z = j`, `Y` has the
density `f_j` on `(0, ∞)`. Let `h, b ≥ 0`, `S_j ≥ 0` for `j ∈ [J]`, and `n ≥ 1`. Then
`E[CPUGS] = Σ_{j∈[J]} ∫_{θ>0} p̃_j(n, θ) C_θj / θ dθ + E[truncated-cycle holding term]`, with
`p̃_j(n, θ)` the corrected biased density `biasedDensity`.

**Correction.** (a) In the printed `p̃_j(n, θ)` the last-cycle term
`χ(Σ_{s=1}^τ Z_s = n − j) / ((Σ_{s∈[τ]} Y_s + θ)/θ)` lacks the factor `χ(Z_{τ+1} = j)` (the next
demand must arrive at `n`) and uses `θ` where the CPUGS denominator has `max{1, X_n} =
max{1, θ}`; it is replaced by `χ(Σ_{s=1}^τ Z_s = n − j) χ(Z_{τ+1} = j) θ / (Σ_{s∈[τ]} Y_s +
max{1, θ})`. (b) As in Theorem 4, the holding cost of a truncated last cycle is added. Counterexample
to the printed identity: `n = 1`, `J = 2`, `p = (1/2, 1/2)`, `f₁ = f₂` uniform on `(1, 2)`,
`h = 0`, `b = 1`, `S₁ = S₂ = 0`: the CPUGS has expectation `1/2`, the printed right side is `1`.

**Formalization Note.** Arbitrary probability space; `(Z t, Y t)` for `t ≥ 1` independent with law
`M.cycleLaw`; all expectations and the `θ`-integral are lower Lebesgue integrals in `ℝ≥0∞`, so
no integrability hypothesis is added (`C_θj/θ` need not be integrable near `0`). The paper's
`∫_θ` is over `(0, ∞)`, where the densities live. The monotonicity `S_{j−1} ≤ S_j` is not
needed and not assumed. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M : ContinuousDemandModel) (Z : ℕ → Ω → ℕ) (Y : ℕ → Ω → ℝ)
    (hZ : ∀ t, Measurable (Z t)) (hY : ∀ t, Measurable (Y t))
    (hind : iIndepFun (fun t ω => (Z (t + 1) ω, Y (t + 1) ω)) P)
    (hlaw : ∀ t, 1 ≤ t → P.map (fun ω => (Z t ω, Y t ω)) = M.cycleLaw)
    (h b : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ b) (S : ℕ → ℝ) (hS : ∀ l ∈ Finset.Icc 1 M.law.J, 0 ≤ S l)
    (n : ℕ) (hn : 1 ≤ n) :
    ∫⁻ ω, ENNReal.ofReal (cpugs h b S Z Y n ω) ∂P =
      (∑ j ∈ Finset.Icc 1 M.law.J, ∫⁻ θ in Set.Ioi 0,
        biasedDensity M P Z Y n j θ * ENNReal.ofReal (sbsCycleCost h b S θ j / θ)) +
      ∫⁻ ω, ENNReal.ofReal (truncatedHolding h S Z Y n ω) ∂P := by sorry

end GamblersFallacy.Supplement
