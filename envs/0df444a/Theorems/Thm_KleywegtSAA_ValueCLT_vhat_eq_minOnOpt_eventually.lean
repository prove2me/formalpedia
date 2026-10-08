-- Prove2me | Theorems.Thm_KleywegtSAA_ValueCLT_vhat_eq_minOnOpt_eventually
-- name    : KleywegtSAA.ValueCLT.vhat_eq_minOnOpt_eventually
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:09:04.481791+00:00
-- url     : https://prove2.me/theorems/508eb554-b18f-4d0f-b15d-e108cdf05032
-- title:
--   §2.2, proof of Proposition 2.3, p. 5 — w.p.1, v̂_N − min_{x∈𝒮*} ĝ_N(x) = 0 for N large enough
-- statement:
--   Let $\mathcal S$ be a nonempty finite set and $G : \mathcal S \times \mathcal W \to \mathbb R$ with $G(x, \cdot)$ measurable and $\mathbb E\,|G(x, W)| < \infty$ for every $x \in \mathcal S$. Let $W^1, W^2, \dots$ be an i.i.d. sample of $W$, let $g(x) = \mathbb E\, G(x, W)$, $\hat g_N(x) = N^{-1}\sum_{n=1}^N G(x, W^n)$, $\hat v_N = \min_{x \in \mathcal S} \hat g_N(x)$, and let $\mathcal S^*$ be the set of minimizers of $g$ over $\mathcal S$. Then for almost every realization $\omega$ of the sample there is an $N(\omega)$ such that for all $N \ge N(\omega)$
--   $$\hat v_N - \min_{x \in \mathcal S^*} \hat g_N(x) = 0.$$
--
--   This is the first step of the proof of Proposition 2.3: eventually the SAA problem is solved by a true optimal solution, so its optimal value is the minimum of the sample average over $\mathcal S^*$.
--
--   **Formalization Note** "With probability one, for $N$ large enough" is "almost surely, eventually in $N$": the threshold $N(\omega)$ depends on the realization. The sample is a $0$-indexed sequence of independent random elements with the law of `W 0`.
-- source:
--   Kleywegt & Shapiro, The sample average approximation method for stochastic discrete optimization, preprint (two-author version, sha256 56657748…), p. 5, §2.2, proof of Proposition 2.3 (the display v̂_N = min_{x∈Ŝ_N} ĝ_N(x) ≥ min_{x∈𝒮*} ĝ_N(x) and the sentence following it)

import Mathlib
import Definitions.Def_KleywegtSAA_ValueCLT_Setting

namespace KleywegtSAA.ValueCLT

open MeasureTheory ProbabilityTheory Filter Topology

/-- Kleywegt–Shapiro, §2.2, proof of Proposition 2.3, p. 5: with probability one, for `N` large
enough, `v̂_N − min_{x ∈ S*} ĝ_N(x) = 0`. -/
theorem vhat_eq_minOnOpt_eventually
    {X : Type*} (S : Finset X) (hS : S.Nonempty)
    {𝒲 : Type*} [MeasurableSpace 𝒲] (G : X → 𝒲 → ℝ) (hG : ∀ x ∈ S, Measurable (G x))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : ℕ → Ω → 𝒲) (hWm : ∀ n, Measurable (W n)) (hind : iIndepFun W P)
    (hid : ∀ n, IdentDistrib (W n) (W 0) P P)
    (hint : ∀ x ∈ S, Integrable (fun ω => G x (W 0 ω)) P) :
    ∀ᵐ ω ∂P, ∀ᶠ N in atTop,
      S.inf' hS (KleywegtSAA.ExpRate.sampleObj G W N ω) - minOnOpt S hS G P W N ω = 0 := by sorry

end KleywegtSAA.ValueCLT
