-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_mixing_time_transition
-- name    : JuHardCoreTransition.Mixing.mixing_time_transition
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:17:55.645026+00:00
-- url     : https://prove2.me/theorems/b04cb445-16fc-4db6-8e30-beaf599c3d7c
-- title:
--   Theorem 1.4 — the sharp Glauber mixing-time transition (lower bound and polynomial-window characterisation)
-- statement:
--   There is an absolute constant $c>0$ such that, for every fixed $d\ge3$, there are constants $a_d>0$ and $\delta_{\mathrm{mix}}(d)>0$ with the following property. For every $n\ge d+1$ and every rational $0\le\delta\le\delta_{\mathrm{mix}}(d)$, at fugacity $\lambda=(1+\delta)\lambda_c(d)$,
--   $$\max_Gt^G_{\mathrm{mix}}(1/4)\ge a_dn^{3/2}\exp\Big\{\frac{cn\delta^2}d\Big\},$$
--   where $t^G_{\mathrm{mix}}(1/4)$ is the mixing time of Glauber dynamics for $\mu_{G,\lambda}$ from the worst initial state and the maximum is over simple $n$-vertex graphs of maximum degree $d$. Together with the mixing-time bound of Theorem 2.4, for any sequence of rationals $0\le\delta_n\le\delta_{\mathrm{mix}}(d)$, the worst-case Glauber mixing time at fugacity $(1+\delta_n)\lambda_c(d)$ is polynomial in $n$ if and only if
--   $$\delta_n=O\Big(\sqrt{\frac{d\log n}n}\Big).$$
--   The sequence need not be monotone or computable.
--
--   Differences from the source:
--   - encoding: the maximum over simple n-vertex graphs of maximum degree d → worstTmix d n λ: Finset.sup over all SimpleGraph (Fin n) with maxDegree = d; reason: labelled graphs on Fin n; the mixing time is isomorphism-invariant and the class is nonempty for n ≥ d + 1
--   - encoding: polynomial in n → ∃ A, k, n₀ with worstTmix ≤ A n^k for all n ≥ n₀ (and n ≥ d + 1); reason: definition of polynomial growth; constants may depend on d and the sequence
--   - encoding: δ_n = O(√(d log n / n)) → ∃ B, n₀ with δ_n ≤ B √(d log n / n) for all n ≥ n₀; reason: δ_n ≥ 0, so this is the big-O condition
--   - encoding: one pair of constants a_d, δ_mix(d) for both statements → ∃ a, δmix once, used in both conjuncts; reason: as printed: the second sentence refers to the same δ_mix(d)
--   - encoding: t_rel = 1/(1−θ₂), t_mix from the worst initial state → trelG = 1/gap and tmixG = tmix of the published heat-bath kernel hcP at constant activity; reason: the published gap counts eigenvalue 1 with multiplicity; the chain is irreducible, so 1 − gap is θ₂
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Theorem 1.4, printed p.3 / PDF p.4

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GlauberHardCore

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Theorem 1.4 (Mixing-time transition)** (printed p.3 / PDF p.4). There is an absolute
constant `c > 0` such that for every fixed `d ≥ 3` there are constants `a_d > 0` and
`δ_mix(d) > 0` with the following properties.
1. For every `n ≥ d + 1` and every rational `0 ≤ δ ≤ δ_mix(d)`, at `λ = (1 + δ)λ_c(d)`,
   `max_G t_mix^G(1/4) ≥ a_d n^{3/2} exp(c n δ²/d)`, the maximum over simple graphs on `n`
   vertices of maximum degree `d`, `t_mix^G(1/4)` the worst-start mixing time of the single-site
   Glauber dynamics for `μ_{G,λ}`.
2. For every sequence of rationals `0 ≤ δ_n ≤ δ_mix(d)`, the worst-case Glauber mixing time at
   fugacity `(1 + δ_n)λ_c(d)` is polynomial in `n` if and only if `δ_n = O(√(d log n / n))`.
"Polynomial in `n`": `≤ A n^k` for all large `n`; `O(·)`: `δ_n ≤ B √(d log n/n)` for all large
`n`. The sequence need not be monotone or computable. -/
theorem mixing_time_transition :
    ∃ c : ℝ, 0 < c ∧ ∀ d : ℕ, 3 ≤ d → ∃ a δmix : ℝ, 0 < a ∧ 0 < δmix ∧
      (∀ n : ℕ, d + 1 ≤ n → ∀ δ : ℚ, 0 ≤ δ → (δ : ℝ) ≤ δmix →
        a * (n : ℝ) ^ (3 / 2 : ℝ) * Real.exp (c * (n : ℝ) * (δ : ℝ) ^ 2 / d) ≤
          (worstTmix d n ((1 + (δ : ℝ)) * lamCrit d) : ℝ)) ∧
      ∀ δs : ℕ → ℚ, (∀ n, 0 ≤ δs n ∧ (δs n : ℝ) ≤ δmix) →
        ((∃ A : ℝ, ∃ k : ℕ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → d + 1 ≤ n →
            (worstTmix d n ((1 + (δs n : ℝ)) * lamCrit d) : ℝ) ≤ A * (n : ℝ) ^ k) ↔
          (∃ B : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
            (δs n : ℝ) ≤ B * Real.sqrt ((d : ℝ) * Real.log n / n))) := by sorry

end JuHardCoreTransition.Mixing
