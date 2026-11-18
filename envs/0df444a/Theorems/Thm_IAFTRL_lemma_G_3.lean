-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_3
-- name    : IAFTRL.lemma_G_3
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T14:19:24.155928+00:00
-- url     : https://prove2.me/theorems/7e20532c-af9c-4c1f-be26-28c686ef03de
-- title:
--   Lemma G.3 — Laplace decay of the GIA-FTRL reference measure away from the optimal action
-- statement:
--   **Setting.** The sharp corrupted instance of Proposition 3.1 / G.1. Here $\mathcal A$ is a compact action set in the Euclidean unit ball that spans $\mathbb R^d$, and $\mathcal B\subseteq\mathcal A$ is a compact generator ($\mathcal A\subseteq\mathrm{Conv}\,\mathcal B$) with $k=\dim\mathcal K\ge1$, where $\mathcal K=\mathrm{Conv}\,\mathcal B$. The direction enumeration $e:\mathbb N\to\mathbb Q^d$ is surjective, and $\|\theta\|_{\mathcal A}\le1$. The action $a^*\in\mathcal A$ is the unique optimal action, the instance is sharp, and $\Delta(a)=(a-a^*)^\top\theta$. The reference measure is $\mu=\sum_{j\in J}\pi_j\delta_{b_j}+\omega_\mu\mu_{16}$ of (3.3), and the learning rate is $\beta_n=16d+\sqrt n$.
--
--   **Claim (existential-constant form).** There is a constant $A$, depending only on the instance, such that the following holds for every round $n\ge1$ and every vector $S\in\mathbb R^d$. If $(a-a^*)^\top S\ge4n^{7/8}\Delta(a)$ for all $a\in\mathcal K$, then
--   $$\int_{a\ne a^*}\exp\!\Big(-\frac{(a-a^*)^\top S}{2\beta_n}\Big)\,\mu(da)\ \le\ \frac{A}{n^3}.$$
--
--   **Formalization Note.** The paper proves the stronger decay $\pi^*A_Lt^{-6}$ for $t\ge T_*$. The weaker $n^{-3}$ for all $n\ge1$ follows by enlarging the constant. It suffices for the summations in Lemmas G.1, G.4 and G.5.
--
--   **Proof idea.**
--   1. The integrand is at most $e^{-\lambda\Delta(a)}$ with $\lambda=2n^{7/8}/\beta_n\gtrsim n^{3/8}$.
--   2. **Atomic part.** The reinforced priorities $h_j\ge j+2+\exp(\|b_j-a^*\|_{\mathcal S}^{-8})$ for $j>j^*$, together with sharpness, give the atomic cap $\sum_{j\ne j^*,\Delta(b_j)\le z}\pi_j\le C_{\rm at}z^{16}$ of (G.50).
--   3. **Volume part.** The affine contraction toward a maximizer of $\Delta$ gives the volume cap $\lambda_{\mathcal K}\{\Delta<z\}\le kz/\Delta^{\mathcal K}_{\max}$. Then $\mu_{16}$ is the law of a mean of 16 independent volume samples, and $\int e^{-\lambda\Delta}d\mu_{16}=(\int e^{-\lambda\Delta/16}d\lambda_{\mathcal K})^{16}$.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.2.1, Lemma G.3, (G.64)–(G.75), with Lemma G.2 (G.50)–(G.62)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.3 (Laplace decay away from the optimal action).** Zhao–Tan, *Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.3, p.129:
"If `t ≥ T*` and `X_t(a) ≥ 4t^{7/8}Δ(a)` for all `a ∈ K`, then
`(1/π*) ∫_{a≠a*} e^{−X_t(a)/(2β_t)} µ(da) ≤ A_L t^{−6}`."

Existential-constant form with the weaker decay `n^{−3}`, valid for every `n ≥ 1`: there is `A`
(depending only on the instance) such that for every round `n ≥ 1` and every cumulative estimate
`S` with `(a − a*)ᵀS ≥ 4 n^{7/8} Δ(a)` on `𝒦 = Conv ℬ`, where `Δ(a) = (a − a*)ᵀθ`,
`∫_{a ≠ a*} exp(−(a − a*)ᵀS/(2β_n)) µ(da) ≤ A n^{−3}`. -/
theorem lemma_G_3 {d : ℕ} (hd : 1 ≤ d) (𝒜 ℬ : Set (Fin d → ℝ)) (e : ℕ → Fin d → ℚ)
    (h𝒜 : IsCompact 𝒜) (hℬ : IsCompact ℬ) (hgen : IsGenerator 𝒜 ℬ)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (hk : 1 ≤ kdim ℬ)
    (he : Function.Surjective e) (θ astar : Fin d → ℝ) (hθ : setNorm 𝒜 θ ≤ 1)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ A : ℝ, ∀ (n : ℕ) (S : Fin d → ℝ), 1 ≤ n →
      (∀ a ∈ Kset ℬ, 4 * (n : ℝ) ^ ((7 : ℝ) / 8) * ((a - astar) ⬝ᵥ θ) ≤ (a - astar) ⬝ᵥ S) →
      ∫ a in {astar}ᶜ, Real.exp (-((a - astar) ⬝ᵥ S) / (2 * gbeta d n)) ∂(refMu ℬ e) ≤
        A / (n : ℝ) ^ 3 := by sorry

end IAFTRL
