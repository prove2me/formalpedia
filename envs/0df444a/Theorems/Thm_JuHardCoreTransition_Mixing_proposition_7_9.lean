-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_proposition_7_9
-- name    : JuHardCoreTransition.Mixing.proposition_7_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:40.233287+00:00
-- url     : https://prove2.me/theorems/532199e9-7e42-4ccd-adc7-da5429782743
-- title:
--   Proposition 7.9 — local rate bounds and global tails
-- statement:
--   Fix $d\ge3$ and let $b^*_t(\rho)$ be the stable local maximiser of Lemma 7.8. There are a fixed interior neighbourhood $U$ of $(0,b_c)$ and positive constants $c,C,t_0$ such that, for $0\le t\le t_0$ and on $U$,
--   $$\psi_t(\rho,b)\le\psi_t(\rho,b^*_t(\rho))-c\|b-b^*_t(\rho)\|^2,\qquad \psi_t(\rho,b^*_t(\rho))-\psi_t(0,b_c)\le Ct^2+Ct\rho^2-c\rho^4 .$$
--   For types in $U$ with $\mathbb E_0Z_{G_v}(\alpha)>0$, $\log\mathbb E_0Z_{G_v}(\alpha)=\frac N2\psi_t(\rho,b)-\frac32\log N+O_d(1)$. For every type in the domain of (7.4), $\mathbb E_0Z_{G_v}(\alpha)\le N^{C_d}e^{N\psi_t(\rho,b)/2}$ for some $C_d>0$. Outside $U$, $\psi_t(\rho,b)\le\psi_t(0,b_c)-c$ (after possibly decreasing $t_0$). The fugacity is $\lambda=\lambda_c(d)e^t$.
--
--   Differences from the source:
--   - encoding: b*_t(ρ), the maximiser constructed in Lemma 7.8 → an existential bstar analytic on W with IsStableMaximizer d B W, with b ∈ B and (ρ,t) ∈ W throughout U × [0,t₀]; reason: this states the defining analytic local-maximizer property and ties every evaluated parameter to its domain, without importing a draft theorem
--   - encoding: a fixed interior neighbourhood U of (0, b_c) → an open U ∋ (0, b_c) contained in InRateDomain, with every type proportion positive; reason: the domain of (7.4) requires a feasible coupling as well as nonnegative proportions; U is an interior neighborhood of that domain
--   - encoding: ‖b − b*_t(ρ)‖² → (b₁ − b*₁)² + (b₂ − b*₂)²; reason: Euclidean norm written out
--   - encoding: O_d(1) in (7.33) → ∃ K, N₀ (before N, t and the type): |log E_0 Z − (N/2)ψ_t + (3/2) log N| ≤ K for even N ≥ N₀; reason: uniform big-O: the constant and the size cutoff are chosen before every varying parameter, as the paper's standing convention prescribes
--   - encoding: every type in the domain of (7.4); for some C_d > 0 → every integer type (counts summing to an even N > 0) whose (ρ, b) satisfies InRateDomain, for all 0 ≤ t ≤ t₀, with one C_d > 0; reason: the global bound is stated in the proposition's range 0 ≤ t ≤ t₀
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Proposition 7.9, printed p.67 / PDF p.68

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_HardCore
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate

namespace JuHardCoreTransition.Mixing

open HiddenHardCoreColoring.Mixing

/-- **Proposition 7.9** (printed p.67 / PDF p.68). Fix `d ≥ 3`, and let `b*_t(ρ)` be the stable
local maximiser of Lemma 7.8 (unique local maximiser of `ψ_t(ρ, ·)` in a neighbourhood `B` of
`b_c`, for `(ρ, t)` in a neighbourhood `W` of `(0, 0)`). There are a fixed interior neighbourhood
`U` of `(0, b_c)` and constants `c, C, t₀ > 0` such that for `0 ≤ t ≤ t₀` and `(ρ, b) ∈ U`:
* (7.31) `ψ_t(ρ, b) ≤ ψ_t(ρ, b*_t(ρ)) − c‖b − b*_t(ρ)‖²`;
* (7.32) `ψ_t(ρ, b*_t(ρ)) − ψ_t(0, b_c) ≤ Ct² + Ctρ² − cρ⁴`;
* (7.33) for integer types in `U` with `E_0 Z_{G_v}(α) > 0`,
  `log E_0 Z_{G_v}(α) = (N/2) ψ_t(ρ, b) − (3/2) log N + O_d(1)`;
* for every integer type in the domain of (7.4), `E_0 Z_{G_v}(α) ≤ N^{C_d} e^{N ψ_t(ρ,b)/2}` for
  some `C_d > 0`;
* outside `U`, `ψ_t(ρ, b) ≤ ψ_t(0, b_c) − c`.
The fugacity is `λ = λ_c(d) e^t`. -/
theorem proposition_7_9 (d : ℕ) (hd : 3 ≤ d) :
    ∃ B : Set (ℝ × ℝ), B ∈ nhds (bC d) ∧
    ∃ W : Set (ℝ × ℝ), W ∈ nhds ((0 : ℝ), (0 : ℝ)) ∧
    ∃ bstar : ℝ → ℝ → ℝ × ℝ, IsStableMaximizer d B W bstar ∧
      (∀ p ∈ W, AnalyticAt ℝ (fun q : ℝ × ℝ => bstar q.2 q.1) p) ∧
    ∃ U : Set (ℝ × (ℝ × ℝ)), IsOpen U ∧ ((0 : ℝ), bC d) ∈ U ∧
      (∀ x ∈ U, InRateDomain x.1 x.2 ∧ ∀ a, 0 < typeOf x.1 x.2 a) ∧
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ∀ x ∈ U, x.2 ∈ B ∧ (x.1, t) ∈ W) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ∀ x ∈ U,
        psi d t x.1 x.2 ≤ psi d t x.1 (bstar t x.1) -
          c * ((x.2.1 - (bstar t x.1).1) ^ 2 + (x.2.2 - (bstar t x.1).2) ^ 2)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ∀ x ∈ U,
        psi d t x.1 (bstar t x.1) - psi d t 0 (bC d) ≤ C * t ^ 2 + C * t * x.1 ^ 2 - c * x.1 ^ 4) ∧
      (∃ K : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ t₀ →
        ∀ n : Fin 4 → ℕ, ∑ a, n a = N → coordsOf (propOf N n) ∈ U →
          0 < E0TypeWeight d N (lamCrit d * Real.exp t) n →
          |Real.log (E0TypeWeight d N (lamCrit d * Real.exp t) n) -
              ((N : ℝ) / 2 * psi d t (coordsOf (propOf N n)).1 (coordsOf (propOf N n)).2 -
                3 / 2 * Real.log N)| ≤ K) ∧
      (∃ Cd : ℝ, 0 < Cd ∧ ∀ N : ℕ, Even N → 0 < N → ∀ t : ℝ, 0 ≤ t → t ≤ t₀ →
        ∀ n : Fin 4 → ℕ, ∑ a, n a = N →
          InRateDomain (coordsOf (propOf N n)).1 (coordsOf (propOf N n)).2 →
          E0TypeWeight d N (lamCrit d * Real.exp t) n ≤
            (N : ℝ) ^ Cd * Real.exp ((N : ℝ) *
              psi d t (coordsOf (propOf N n)).1 (coordsOf (propOf N n)).2 / 2)) ∧
      (∀ t : ℝ, 0 ≤ t → t ≤ t₀ → ∀ (ρ : ℝ) (b : ℝ × ℝ), InRateDomain ρ b → (ρ, b) ∉ U →
        psi d t ρ b ≤ psi d t 0 (bC d) - c) := by sorry

end JuHardCoreTransition.Mixing
