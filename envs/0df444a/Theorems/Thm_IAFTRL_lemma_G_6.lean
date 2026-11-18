-- Prove2me | Theorems.Thm_IAFTRL_lemma_G_6
-- name    : IAFTRL.lemma_G_6
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-17T08:38:19.961299+00:00
-- url     : https://prove2.me/theorems/6600c1f9-d463-4c72-825c-17258c0da567
-- title:
--   Lemma G.6 — finite centered sampling allocations exist under sharpness
-- statement:
--   Let $\mathcal A\subseteq\mathbb B^d$ ($d\ge1$) be a compact action set with $\mathrm{span}(\mathcal A)=\mathbb R^d$. Let $\theta$ have a unique optimal action $a^*\in\mathcal A$, and suppose the instance is sharp on $\mathrm{Conv}(\mathcal A)$: there is $\varsigma>0$ with $(a-a^*)^\top\theta\ge\varsigma\|a-a^*\|_{\mathcal S}$ for all $a\in\mathrm{Conv}(\mathcal A)$, where $\mathcal S=\mathrm{Conv}(\mathcal A\cup(-\mathcal A))$.
--
--   Then the centered program (1.4) is feasible. That is, there is a finite nonnegative Borel measure $n$ on $\mathcal A$ with $H_n=\int aa^\top n(da)\succ0$ and
--   $$
--   \|u-a^*\|^2_{H_n^{-1}}\le\frac{\Delta(u)^2}{2}\qquad\text{for all }u\in\mathrm{Conv}(\mathcal A).
--   $$
--   Consequently $c^*_{\mathrm{ctr}}(\mathcal A,\theta)<\infty$.
--
--   This is the direction "sharpness $\Rightarrow$ finite centered information-acquisition complexity" used to choose a comparison allocation in the proof of Theorem 3.1.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G.6, Lemma G.6 (G.110), p. 134

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL

namespace IAFTRL

open MeasureTheory

/-- **Lemma G.6 (Finite centered sampling allocations under sharpness).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits* (STOC submission version), Lemma G.6, p.134:
"Under sharpness, the centered program is feasible and
`inf_{n centered feasible on 𝒜} c^n_ctr(𝒜, θ) = c*_ctr(𝒜, θ) < ∞` (G.110), where the infimum is
over finite nonnegative sampling allocations."

For a compact action set `𝒜 ⊆ 𝔹^d` spanning `ℝ^d` with unique optimal action `a* ∈ 𝒜` under `θ`,
sharpness (1.3) on `Conv 𝒜` implies that a finite feasible centered sampling allocation exists
(so the infimum defining `c*_ctr` is over a nonempty set of nonnegative costs, hence finite). -/
theorem lemma_G_6 {d : ℕ} (hd : 1 ≤ d) (𝒜 : Set (Fin d → ℝ)) (h𝒜 : IsCompact 𝒜)
    (hball : ∀ a ∈ 𝒜, a ⬝ᵥ a ≤ 1) (hspan : Submodule.span ℝ 𝒜 = ⊤) (θ astar : Fin d → ℝ)
    (hastar : astar ∈ 𝒜) (huniq : ∀ a ∈ 𝒜, a ≠ astar → astar ⬝ᵥ θ < a ⬝ᵥ θ)
    (hsharp : IsSharp 𝒜 θ astar) :
    ∃ n : Measure (Fin d → ℝ), IsCtrAlloc 𝒜 θ astar n := by sorry

end IAFTRL
