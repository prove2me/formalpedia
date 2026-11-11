-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_theorem_8_4
-- name    : JuHardCoreTransition.Mixing.theorem_8_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:48.735468+00:00
-- url     : https://prove2.me/theorems/49b82fb1-dd84-4a6f-b35f-831f401b88d7
-- title:
--   Theorem 8.4 — one-gadget second moments
-- statement:
--   There are a positive smooth function $C_d^{pm}(\alpha,\beta)$, computed in (8.18), and a compact neighbourhood $U_d$ of $\alpha_c$ within the positive probability vectors on $\Omega$ such that the coordinates $(\rho,b)$ of every $\alpha\in U_d$ lie in the neighbourhood $U$ fixed in Definition 7.1, and, uniformly for integer types $\alpha,\beta\in U_d$, as even $N\to\infty$,
--   $$\frac{\mathbb E_0[Z_{G_v}(\alpha)Z_{G_v}(\beta)]}{\mathbb E_0Z_{G_v}(\alpha)\,\mathbb E_0Z_{G_v}(\beta)}=C_d^{pm}(\alpha,\beta)\big[1+O_d(N^{-1/2})\big].$$
--   The estimate holds at every positive fugacity, without a restriction on $N\delta^2$. Here $C_d^{pm}(\alpha,\beta)=\det(I-A_{\mathrm{col}}\otimes T_{\alpha,\perp}\otimes T_{\beta,\perp})^{-1/2}$.
--
--   Differences from the source:
--   - generalization: the coordinates of U_d lie in the neighbourhood U fixed in Definition 7.1 → U is an arbitrary neighbourhood of (0, b_c) given as a hypothesis, and U_d is chosen inside it; reason: Definition 7.1 fixes U only as a neighbourhood with further properties; taking that U gives the source statement
--   - encoding: a positive smooth function C_d^{pm} → coeffPM d positive on U_d × U_d and ContDiffOn ℝ ∞, in the (ρ, b) coordinates of both types, on an open set containing U_d × U_d; reason: smoothness in the simplex coordinates
--   - encoding: compact neighbourhood of α_c within the positive probability vectors → IsCompact U_d, U_d ∈ nhdsWithin α_c (simplex), and every α ∈ U_d is a probability vector with positive entries; reason: definition of the phrase
--   - encoding: T_{α,⊥}, the restriction of T_α to L²₀(α) → T_α Π_α on ℝ^Ω, Π_α f = f − (Σ α_b f(b))·1; reason: T_α Π_α is 0 on constants and T_α on L²₀(α), so the determinant in (8.18) is unchanged
--   - encoding: C^{pm}[1 + O_d(N^{-1/2})] uniformly in integer types and at every positive fugacity → ∃ C, N₀ before λ, N and the types: |ratio − C^{pm}| ≤ C·C^{pm}/√N; reason: uniform big-O: the constant and the size cutoff are chosen before every varying parameter, as the paper's standing convention prescribes
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Theorem 8.4, printed p.80 / PDF p.81

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate

namespace JuHardCoreTransition.Mixing

/-- **Theorem 8.4 (One-gadget second moments)** (printed p.80 / PDF p.81). Fix `d ≥ 3` and a
neighbourhood `U` of `(0, b_c)` (in the source, the neighbourhood fixed in Definition 7.1). There
are a compact neighbourhood `U_d` of `α_c` within the positive probability vectors on `Ω`, whose
types have coordinates `(ρ, b)` in `U`, such that `C_d^{pm}(α, β)` of (8.18) is positive on
`U_d × U_d` and smooth near it, and, uniformly for integer types `α, β ∈ U_d` and at every
fugacity `λ > 0`, as even `N → ∞`,
`E_0[Z_{G_v}(α) Z_{G_v}(β)] / (E_0 Z_{G_v}(α) E_0 Z_{G_v}(β)) = C_d^{pm}(α, β)[1 + O_d(N^{−1/2})]`.
Smoothness is stated in the coordinates `(ρ, b)` of the two types. -/
theorem theorem_8_4 (d : ℕ) (hd : 3 ≤ d) (U : Set (ℝ × (ℝ × ℝ)))
    (hU : U ∈ nhds ((0 : ℝ), bC d)) :
    ∃ Ud : Set (Fin 4 → ℝ), IsCompact Ud ∧
      Ud ∈ nhdsWithin (alphaC d) {α : Fin 4 → ℝ | ∑ a, α a = 1} ∧
      (∀ α ∈ Ud, (∑ a, α a = 1) ∧ ∀ a, 0 < α a) ∧
      (∀ α ∈ Ud, coordsOf α ∈ U) ∧
      (∀ α ∈ Ud, ∀ β ∈ Ud, 0 < coeffPM d α β) ∧
      (∃ O : Set ((ℝ × (ℝ × ℝ)) × (ℝ × (ℝ × ℝ))), IsOpen O ∧
        (∀ α ∈ Ud, ∀ β ∈ Ud, (coordsOf α, coordsOf β) ∈ O) ∧
        ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p => coeffPM d (typeOf p.1.1 p.1.2) (typeOf p.2.1 p.2.2)) O) ∧
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ lam : ℝ, 0 < lam → ∀ N : ℕ, Even N → N₀ ≤ N →
        ∀ n m : Fin 4 → ℕ, ∑ a, n a = N → ∑ a, m a = N →
          propOf N n ∈ Ud → propOf N m ∈ Ud →
          |E0TypeWeight2 d N lam n m / (E0TypeWeight d N lam n * E0TypeWeight d N lam m) -
              coeffPM d (propOf N n) (propOf N m)| ≤
            C * coeffPM d (propOf N n) (propOf N m) / Real.sqrt N := by sorry

end JuHardCoreTransition.Mixing
