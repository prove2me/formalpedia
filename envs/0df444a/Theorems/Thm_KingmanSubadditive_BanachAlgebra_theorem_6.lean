-- Prove2me | Theorems.Thm_KingmanSubadditive_BanachAlgebra_theorem_6
-- name    : KingmanSubadditive.BanachAlgebra.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:20:04.798023+00:00
-- url     : https://prove2.me/theorems/a8b2a6c8-39ba-400c-8f9d-4e703e665b3c
-- title:
--   Theorem 6, p. 893 — for stationary (Y_n) in a Banach algebra with E(log‖Y₁‖)⁺ < ∞, n⁻¹ log‖Y₁⋯Y_n‖ → ξ a.s. and E(ξ) = lim n⁻¹E log‖Y₁⋯Y_n‖
-- statement:
--   Let $\mathfrak B$ be a real or complex Banach algebra and let $(Y_n)_{n\ge1}$ be a stationary sequence of random elements of $\mathfrak B$ on a probability space $(\Omega,\mathcal F,P)$. Suppose that
--   $$E\{(\log\|Y_1\|)^+\}<\infty. \tag{2.3.3}$$
--   Then the limit
--   $$\xi=\lim_{n\to\infty}n^{-1}\log\|Y_1Y_2\cdots Y_n\| \tag{2.3.4}$$
--   exists in $-\infty\le\xi<\infty$ with probability one, and
--   $$E(\xi)=\lim_{n\to\infty}n^{-1}E\{\log\|Y_1Y_2\cdots Y_n\|\}. \tag{2.3.5}$$
--
--   The quantity $e^{\xi}$ is a stochastic analogue of the spectral radius: if every $Y_n$ equals a fixed element $y$, then $e^\xi$ is the spectral radius of $y$ by Gelfand's formula. For $k\times k$ matrices with any matrix norm the theorem is the Furstenberg–Kesten theorem on products of random matrices.
--
--   **Formalization Note** $\log\|\cdot\|$ is extended-real valued ($\log\|0\|=-\infty$) and all expectations are extended expectations $\int f^+\,dP-\int f^-\,dP\in[-\infty,\infty)$. The conclusion asserts: $\xi$ is a measurable $[-\infty,\infty]$-valued random variable; almost surely $\xi<\infty$ and $n^{-1}\log\|Y_1\cdots Y_n\|\to\xi$ in $[-\infty,\infty]$; $E(\xi^+)<\infty$; and $n^{-1}E\{\log\|Y_1\cdots Y_n\|\}\to E(\xi)$ in $[-\infty,\infty]$, which asserts both that the limit exists and that it equals $E(\xi)$. Stationarity is equality of joint laws on $\mathfrak B^{\mathbb N}$ with the product $\sigma$-algebra; each $Y_n$ is strongly measurable and $\mathfrak B$ need not be separable. $\mathfrak B$ is a complete unital normed ring and a normed algebra over $\mathbb R$ or $\mathbb C$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 893, §2.3, Theorem 6, (2.3.3)–(2.3.5)

import Mathlib
import Definitions.Def_KingmanSubadditive_BanachAlgebra_Process
import Definitions.Def_KingmanSubadditive_BanachAlgebra_RandomProduct

namespace KingmanSubadditive.BanachAlgebra

open MeasureTheory Filter Topology

/-- **Theorem 6, §2.3, p. 893** (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973), DOI 10.1214/aop/1176996798). "Let `(Y_n)` be a stationary sequence taking
values in a (real or complex) Banach algebra `𝔅`, and suppose that (2.3.3)
`E{(log ‖Y₁‖)⁺} < ∞`. Then (2.3.4) `ξ = lim_{n→∞} n⁻¹ log ‖Y₁ Y₂ ⋯ Y_n‖` exists in
`−∞ ≤ ξ < ∞` with probability one, and (2.3.5) `E(ξ) = lim_{n→∞} n⁻¹ E{log ‖Y₁ Y₂ ⋯ Y_n‖}`."

**Formalization Note.** `log ‖·‖` is the extended-real logarithm (`log ‖0‖ = −∞`), so
`log ‖Y₁ ⋯ Y_n‖`, `ξ` and all means are in `EReal`; expectations are the extended expectation
`eMean` (`∫ f⁺ − ∫ f⁻`, possibly `−∞`). The conclusion asserts: `ξ` is a measurable
`EReal`-valued random variable; almost surely `ξ < +∞` and `n⁻¹ log ‖Y₁ ⋯ Y_n‖ → ξ` in `[−∞, ∞]`;
`E(ξ⁺) < ∞` (so `E(ξ)` is defined); and the sequence `n⁻¹ E{log ‖Y₁ ⋯ Y_n‖}` converges to `E(ξ)`
in `[−∞, ∞]` (both existence of the limit and its value). The term at `n = 0` does not affect the
limits. The product is ordered `Y₁ Y₂ ⋯ Y_n`. Each `Y_n` (`n ≥ 1`) is strongly measurable and the
sequence is stationary in the joint-law sense (`IsStationarySeq`); `𝔅` need not be separable. -/
theorem theorem_6 {𝕜 𝔅 Ω : Type*} [RCLike 𝕜] [NormedRing 𝔅]
    [NormedAlgebra 𝕜 𝔅] [CompleteSpace 𝔅] [MeasurableSpace 𝔅] [BorelSpace 𝔅]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → 𝔅)
    (hY : ∀ n : ℕ, 1 ≤ n → StronglyMeasurable (Y n)) (hstat : IsStationarySeq P Y)
    (hlog : ∫⁻ ω, (logNorm (Y 1 ω)).toENNReal ∂P < ⊤) :
    ∃ ξ : Ω → EReal, Measurable ξ ∧
      (∀ᵐ ω ∂P, ξ ω ≠ ⊤ ∧
        Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) * logNorm (prodRange Y 0 n ω))
          atTop (𝓝 (ξ ω))) ∧
      ∫⁻ ω, (ξ ω).toENNReal ∂P < ⊤ ∧
      Tendsto (fun n : ℕ => (((n : ℝ)⁻¹ : ℝ) : EReal) *
          eMean P (fun ω => logNorm (prodRange Y 0 n ω)))
        atTop (𝓝 (eMean P ξ)) := by sorry

end KingmanSubadditive.BanachAlgebra
