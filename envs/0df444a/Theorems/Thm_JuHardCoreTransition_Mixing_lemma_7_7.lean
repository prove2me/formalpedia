-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_7_7
-- name    : JuHardCoreTransition.Mixing.lemma_7_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:40.877919+00:00
-- url     : https://prove2.me/theorems/10518113-ba15-47b7-8568-5f51cc818344
-- title:
--   Lemma 7.7 — expected type weights of one gadget
-- statement:
--   Fix $d\ge3$. There is a positive analytic function $h_d$, independent of $N$ and $\delta$, defined for continuous proportions $\alpha$ whose coordinates $(\rho,b)$ lie in a fixed neighbourhood $U$ of $(0,b_c)$, and bounded above and away from zero there, such that, as $N\to\infty$ through even values, uniformly over integer types $\alpha$ with $(\rho,b)\in U$ and $\mathbb E_0Z_{G_v}(\alpha)>0$, and uniformly over all $\lambda>0$ with $t=\log(\lambda/\lambda_c(d))$,
--   $$\mathbb E_0Z_{G_v}(\alpha)=N^{-3/2}e^{N\psi_t(\rho,b)/2}h_d(\alpha)\big(1+O_d(N^{-1/2})\big).$$
--   Here $\mathbb E_0$ is the law of $d$ independent uniform perfect matchings of $[N]$ and $Z_{G_v}(\alpha)$ the weight of the independent sets of the double cover with type $\alpha$.
--
--   Differences from the source:
--   - encoding: h_d(α), a function of the continuous proportions α → a function h of the coordinates (ρ, b) of α, analytic on U; reason: α ↦ (ρ, b) is an affine bijection of the probability simplex onto its image; same instances
--   - encoding: fixed neighbourhood of (0, b_c); h_d bounded above and away from zero there → U ∈ nhds (0, b_c); constants 0 < m ≤ h ≤ M on U; reason: definition of the phrase
--   - encoding: (1 + O_d(N^{-1/2})) as even N → ∞, uniformly over types and all λ > 0 → ∃ C, N₀ before N, λ and the type: the ratio is 1 + ε with |ε| ≤ C/√N; reason: uniform big-O: the constant and the size cutoff are chosen before every varying parameter, as the paper's standing convention prescribes
--   - encoding: E_0 under the construction law P_0 (matchings with uniform edge orders and orientations) → the uniform average over d-tuples of perfect matchings of Fin N; reason: the type weight Z_{G_v}(α) does not depend on edge orders or orientations
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 7.7, printed p.61 / PDF p.62

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Lemma 7.7 (Expected type weights)** (printed p.61 / PDF p.62). Fix `d ≥ 3`. There are a
fixed neighbourhood `U` of `(ρ, b) = (0, b_c)` and a function `h_d`, analytic on `U` and bounded
above and away from zero there (independent of `N` and `λ`), such that, as `N → ∞` through even
values, uniformly over integer types `α` (counts `n`, `α = n/N`) with coordinates in `U` and
`E_0 Z_{G_v}(α) > 0`, and uniformly over all `λ > 0` with `t = log(λ/λ_c(d))`,
`E_0 Z_{G_v}(α) = N^{−3/2} e^{N ψ_t(ρ,b)/2} h_d(α) (1 + O_d(N^{−1/2}))`.
`h_d` is written as a function of the coordinates `(ρ, b)` of `α`. -/
theorem lemma_7_7 (d : ℕ) (hd : 3 ≤ d) :
    ∃ U : Set (ℝ × (ℝ × ℝ)), U ∈ nhds ((0 : ℝ), bC d) ∧
    ∃ h : ℝ × (ℝ × ℝ) → ℝ, AnalyticOnNhd ℝ h U ∧
    ∃ m M : ℝ, 0 < m ∧ (∀ x ∈ U, m ≤ h x ∧ h x ≤ M) ∧
    ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → ∀ lam : ℝ, 0 < lam →
      ∀ n : Fin 4 → ℕ, ∑ a, n a = N → coordsOf (propOf N n) ∈ U →
        0 < E0TypeWeight d N lam n →
        ∃ ε : ℝ, |ε| ≤ C / Real.sqrt N ∧
          E0TypeWeight d N lam n =
            (N : ℝ) ^ (-(3 / 2 : ℝ)) *
              Real.exp ((N : ℝ) * psi d (Real.log (lam / lamCrit d)) (coordsOf (propOf N n)).1
                (coordsOf (propOf N n)).2 / 2) *
              h (coordsOf (propOf N n)) * (1 + ε) := by sorry

end JuHardCoreTransition.Mixing
