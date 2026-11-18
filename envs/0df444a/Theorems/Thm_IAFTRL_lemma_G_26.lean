-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_26
-- name    : IAFTRL.lemma_G_26
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T14:19:26.214942+00:00
-- url     : https://prove2.me/theorems/ec5735f0-5e69-4023-b511-46537adfc5c0
-- title:
--   Lemma G.26 — good events, ratio moments and the weighted failure bound for corrupted GIA-FTRL
-- statement:
--   **Setting.** The sharp corrupted instance of Proposition 3.1 / G.1. Here $\mathcal A$ is a compact action set in the Euclidean unit ball that spans $\mathbb R^d$, and $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathrm{Conv}\,\mathcal B$) with $k=\dim\mathcal K\ge1$, where $\mathcal K=\mathrm{Conv}\,\mathcal B$. The direction enumeration $e:\mathbb N\to\mathbb Q^d$ is surjective, and $\|\theta\|_{\mathcal A}\le1$. The action $a^*\in\mathcal A$ is the unique optimal action, the instance is sharp, and $\Delta(a)=(a-a^*)^\top\theta$. The reference measure is $\mu=\sum_{j\in J}\pi_j\delta_{b_j}+\omega_\mu\mu_{16}$ of (3.3), and the learning rate is $\beta_n=16d+\sqrt n$.
--
--   **Claim (interface form).** There is a constant $W$, depending only on the instance, with the following property. Take any GIA-FTRL run of $T\ge1$ rounds in the corrupted regime with budget $C\ge0$, with cumulative estimates $X_t(a)=(a-a^*)^\top\sum_{s<t}\hat\theta_s$ (paper round $t$). This run admits measurable events $G_t$ and measurable ratios $L_t,U_t$, both zero off $G_t$, satisfying the following.
--
--   1. **Pointwise comparisons.** On $G_t$, $L_t\ge1$, $U_t\ge0$, and for all $a\in\mathcal K$:
--   $$X_t(a)\ge4t^{7/8}\Delta(a),\qquad\frac{\Delta(a)}{L_t}\le\frac{X_t(a)}{t}\le U_t\Delta(a).$$
--   2. **Ratio moments.** $\mathbb E[L_t^rU_t]\le64^{r+1}$ for $r=1,3,5$.
--   3. **Weighted failure bound.**
--   $$\sum_{t=1}^{T}t^{-1/2}\,\mathbb P(G_t^c)\le W\big(1+\sqrt C\log(e+C)\big).$$
--
--   **Formalization Note.** Rounds are 0-based in Lean: run round $t$ is paper round $t+1$. This is $G_t=G_t^{\rm cor}$ of Lemma G.26, with $L_t=\mathbf 1_{G_t}\max\{1,m_f^{-1}\}$ and $U_t=\mathbf 1_{G_t}R_f$. Item 1 is (G.552) and (G.554), item 2 is (G.551), and item 3 is (G.525) combined with (G.11).
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6, Lemma G.26, (G.525) and (G.550)–(G.561), with (G.8)–(G.11)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.26 (Uniform relative gaps, with a square-root-chargeable failure tail).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.26, pp.174–176:
"`Σ_{t≥1} t^{−1/2} P((G_t^cor)^c) ≤ W_θ √H`. On `G_t^cor` … the ratio moments hold with
`C_rat = 64` …", with (G.550)–(G.554): "`E[L_t^r U_t] ≤ C_rat^{r+1}` (r = 1, 3, 5),
`Δ(a)/L_t ≤ X_t(a)/t ≤ U_t Δ(a)`, `X_t(a) ≥ 4τ_t Δ(a) ≥ 4t^{7/8}Δ(a)`", and (G.11):
`√H ≤ 16[1 + √C log(e + C)]`.

Interface form, with 0-based rounds (run round `t` is the paper's round `t + 1`, with
`X_{t+1}(a) = (a − a*)ᵀ Σ_{s<t} θ̂_s`): in the sharp corrupted setting there is `W` such that
every run admits measurable good events `G_t` and ratios `L_t, U_t` (vanishing off `G_t`) with the
pointwise gap comparisons on `G_t`, the three product moments, and the weighted failure bound
`Σ_t (t+1)^{−1/2} P(G_tᶜ) ≤ W (1 + √C log(e + C))`. -/
theorem lemma_G_26 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ W : ℝ, ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (T : ℕ) (C : ℝ) (R : GRun d Ω), 1 ≤ T → 0 ≤ C →
        IsGIAFTRLRun P 𝒜 ℬ e T R → IsCorruptedG P 𝒜 θ C T R →
        ∃ (G : ℕ → Set Ω) (L U : ℕ → Ω → ℝ),
          (∀ t, MeasurableSet (G t)) ∧ (∀ t, Measurable (L t)) ∧ (∀ t, Measurable (U t)) ∧
          (∀ t < T, ∀ ω ∈ G t, 1 ≤ L t ω ∧ 0 ≤ U t ω ∧ ∀ a ∈ Kset ℬ,
            4 * ((t + 1 : ℕ) : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤
              (a - astar) ⬝ᵥ R.cumEst t ω ∧
            (a - astar) ⬝ᵥ θ ≤ L t ω * ((a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1)) ∧
            (a - astar) ⬝ᵥ R.cumEst t ω / ((t : ℝ) + 1) ≤ U t ω * ((a - astar) ⬝ᵥ θ)) ∧
          (∀ t < T, ∀ ω ∉ G t, L t ω = 0 ∧ U t ω = 0) ∧
          (∀ t < T, ∀ r ∈ ({1, 3, 5} : Finset ℕ),
            Integrable (fun ω => L t ω ^ r * U t ω) P ∧
            ∫ ω, L t ω ^ r * U t ω ∂P ≤ 64 ^ (r + 1)) ∧
          ∑ t ∈ Finset.range T, (Real.sqrt ((t : ℝ) + 1))⁻¹ * (P (G t)ᶜ).toReal ≤
            W * (1 + Real.sqrt C * Real.log (Real.exp 1 + C)) := by sorry

end IAFTRL
