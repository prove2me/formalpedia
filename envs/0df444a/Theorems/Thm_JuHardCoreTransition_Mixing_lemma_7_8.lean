-- Prove2me | Theorems.Thm_JuHardCoreTransition_Mixing_lemma_7_8
-- name    : JuHardCoreTransition.Mixing.lemma_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:16:37.184082+00:00
-- url     : https://prove2.me/theorems/70abd2d5-e16e-495a-bbf5-870139f9c455
-- title:
--   Lemma 7.8 — analytic rate, stable maximiser and quartic expansion
-- statement:
--   Fix $d\ge3$. The function $(\rho,b,t)\mapsto\psi_t(\rho,b)$ is analytic near $(0,b_c,0)$ and $\nabla_b^2\psi_0(0,b_c)=-H_d$. For each sufficiently small $\rho,t$ the function $b\mapsto\psi_t(\rho,b)$ has a unique local maximiser $b^*_t(\rho)$ in a fixed neighbourhood of $b_c$, and $b^*_t(\rho)$ depends analytically on $(\rho,t)$. For fixed $R,W>0$, uniformly on $|r|\le R$, $\|s\|_\infty\le W$,
--   $$\frac N2\big[\psi_t(\rho,b)-\psi_t(0,b^*_t(0))\big]=2Nt^2V_d(r)-\tfrac12s^\top H_ds+O_{d,R,W}(N^{-1/4}),$$
--   where $t=\hat\delta=\log(1+\delta)$, $r=\rho/\sqrt t$, $s=\sqrt{N/2}\,(b-b^*_t(\rho))$, and the error is uniform for $L=2N\delta^2$ between fixed positive bounds.
--
--   Differences from the source:
--   - encoding: analytic near (0, b_c, 0) → AnalyticAt ℝ at (0, b_c, 0) of (ρ, b, t) ↦ ψ_t(ρ, b); reason: analyticity at a point is analyticity on a neighbourhood
--   - encoding: ∇²_b ψ_0(0, b_c) = −H_d → iteratedFDeriv ℝ 2 of b ↦ ψ_0(0, b) at b_c, evaluated at (u, v), equals −H_d(u, v) for all u, v; reason: the Hessian as a bilinear form
--   - encoding: for sufficiently small ρ, t a unique local maximiser b*_t(ρ) in a fixed neighbourhood of b_c, analytic in (ρ, t) → ∃ B ∈ nhds b_c, W ∈ nhds (0, 0), bstar with IsStableMaximizer d B W bstar and bstar analytic at every point of W; reason: "sufficiently small" is membership in the neighbourhood W
--   - encoding: O_{d,R,W}(N^{-1/4}), uniform for L = 2Nδ² between fixed positive bounds → ∀ R, W > 0 and 0 < L₁ ≤ L₂, ∃ C, N₀, for even N ≥ N₀, δ > 0 with L₁ ≤ 2Nδ² ≤ L₂: |error| ≤ C N^{-1/4}; reason: uniform big-O: the constant and the size cutoff are chosen before every varying parameter, as the paper's standing convention prescribes
--   - encoding: ‖s‖_∞ ≤ W → both coordinates of s bounded by W in absolute value; reason: definition of the sup norm
-- source:
--   Ju, Liu and Yin, Fine-Grained Complexity Across the Computational Phase Transition, arXiv:2611.02702, pinned source.pdf dated 2026-11-02, SHA256 6288a2d2b0acc0256c0a8e1e8ea59eb0fbfff70c6d282c1c83eacf59cecd3678 (arXiv version suffix not supplied; unverified), Lemma 7.8, printed p.61 / PDF p.62

import Mathlib
import Definitions.Def_JuHardCoreTransition_Mixing_GadgetRate

namespace JuHardCoreTransition.Mixing

/-- **Lemma 7.8** (printed p.61 / PDF p.62). Fix `d ≥ 3`.
1. `(ρ, b, t) ↦ ψ_t(ρ, b)` is analytic near `(0, b_c, 0)`, and `∇²_b ψ_0(0, b_c) = −H_d`.
2. There are a fixed neighbourhood `B` of `b_c`, a neighbourhood `W` of `(ρ, t) = (0, 0)` and a map
   `b*_t(ρ)` such that for `(ρ, t) ∈ W`, `b*_t(ρ)` is the unique local maximiser of
   `b ↦ ψ_t(ρ, b)` in `B`; `b*` depends analytically on `(ρ, t)`.
3. For fixed `R, W > 0` and fixed bounds `0 < L₁ ≤ L₂`, uniformly for `L = 2Nδ² ∈ [L₁, L₂]`,
   `t = log(1 + δ)`, `r = ρ/√t`, `s = √(N/2)(b − b*_t(ρ))`, `|r| ≤ R`, `‖s‖_∞ ≤ W`:
   `(N/2)[ψ_t(ρ, b) − ψ_t(0, b*_t(0))] = 2N t² V_d(r) − ½ sᵀ H_d s + O_{d,R,W}(N^{−1/4})`. -/
theorem lemma_7_8 (d : ℕ) (hd : 3 ≤ d) :
    AnalyticAt ℝ (fun p : ℝ × (ℝ × ℝ) × ℝ => psi d p.2.2 p.1 p.2.1) ((0 : ℝ), bC d, (0 : ℝ)) ∧
    (∀ u v : ℝ × ℝ,
      iteratedFDeriv ℝ 2 (fun b : ℝ × ℝ => psi d 0 0 b) (bC d) ![u, v] = -hessForm d u v) ∧
    ∃ B : Set (ℝ × ℝ), B ∈ nhds (bC d) ∧
    ∃ W : Set (ℝ × ℝ), W ∈ nhds ((0 : ℝ), (0 : ℝ)) ∧
    ∃ bstar : ℝ → ℝ → ℝ × ℝ, IsStableMaximizer d B W bstar ∧
      (∀ p ∈ W, AnalyticAt ℝ (fun q : ℝ × ℝ => bstar q.2 q.1) p) ∧
      ∀ R Wc L₁ L₂ : ℝ, 0 < R → 0 < Wc → 0 < L₁ → L₁ ≤ L₂ →
        ∃ C : ℝ, ∃ N₀ : ℕ, ∀ N : ℕ, Even N → N₀ ≤ N → ∀ δ : ℝ, 0 < δ →
          L₁ ≤ 2 * (N : ℝ) * δ ^ 2 → 2 * (N : ℝ) * δ ^ 2 ≤ L₂ →
          ∀ (ρ : ℝ) (b : ℝ × ℝ),
            |ρ / Real.sqrt (Real.log (1 + δ))| ≤ R →
            |Real.sqrt ((N : ℝ) / 2) * (b.1 - (bstar (Real.log (1 + δ)) ρ).1)| ≤ Wc →
            |Real.sqrt ((N : ℝ) / 2) * (b.2 - (bstar (Real.log (1 + δ)) ρ).2)| ≤ Wc →
            |(N : ℝ) / 2 * (psi d (Real.log (1 + δ)) ρ b -
                  psi d (Real.log (1 + δ)) 0 (bstar (Real.log (1 + δ)) 0)) -
                (2 * (N : ℝ) * Real.log (1 + δ) ^ 2 *
                    quarticV d (ρ / Real.sqrt (Real.log (1 + δ))) -
                  1 / 2 * hessForm d (Real.sqrt ((N : ℝ) / 2) • (b - bstar (Real.log (1 + δ)) ρ))
                    (Real.sqrt ((N : ℝ) / 2) • (b - bstar (Real.log (1 + δ)) ρ)))| ≤
              C * (N : ℝ) ^ (-(1 / 4 : ℝ)) := by sorry

end JuHardCoreTransition.Mixing
