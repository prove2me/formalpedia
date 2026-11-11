-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_corollary_3_6
-- name    : MixedVolFPRAS.Main.corollary_3_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:31:59.932304+00:00
-- url     : https://prove2.me/theorems/ccaeabb1-3ccb-4a97-9529-eb56de7a0da5
-- title:
--   Corollary 3.6 — Poincaré inequality Var_µ[f] ≤ ∫‖∇_{Sⁿ⁻¹} f‖² dµ for the measure µ of Eq. (4)
-- statement:
--   Let $n\ge3$ and let $K_1,\dots,K_{n-3}\subseteq\mathbb{R}^n$ be convex bodies with $h_{K_i}$ smooth on $\mathbb{R}^n\setminus\{0\}$ and $D^2h_{K_i}(\theta)\succ0$ for every $\theta\in S^{n-1}$, and let $\mu$ be the probability measure of Eq. (4). Then for every $f\in C^2(S^{n-1})$
--
--   $$\mathrm{Var}_\mu[f]\le\int_{S^{n-1}}\|\nabla_{S^{n-1}}f\|_2^2\,d\mu .$$
--
--   It follows from the Shenfeld–van Handel spectral gap (Theorem 3.5) and supplies the Poincaré constant $\gamma=1$ needed to sample from $\mu$ with the Metropolis chain of Appendix B.
--
--   Differences from the source:
--   - reading: "the probability measure µ defined in Eq. (4)" → the hypotheses of Eq. (4) (convex bodies, $h_{K_i}$ $C^\infty$ on $\mathbb{R}^n\setminus\{0\}$, $D^2h_{K_i}\succ0$ on $S^{n-1}$, $n\ge3$) are binders; reason: §3.1 states them once above Eq. (4).
--   - encoding: $f\in C^2(S^{n-1})$ → `IsC2OnSphere f` (the 1-homogeneous extension is $C^2$ on $\mathbb{R}^n\setminus\{0\}$); reason: footnote 3, p. 13, is the paper's own definition.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 14, Corollary 3.6

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant
import Definitions.Def_MixedVolFPRAS_Main_Sphere
import Definitions.Def_MixedVolFPRAS_Main_MuMeasure

open scoped ContDiff

namespace MixedVolFPRAS.Main

/-- **Corollary 3.6.** Let `n ≥ 3` and let `K₁, …, K_{n−3}` be convex bodies in `ℝⁿ` with `h_{Kᵢ}`
smooth on `ℝⁿ \ {0}` and `D²h_{Kᵢ}(θ)` positive definite for every `θ ∈ Sⁿ⁻¹`. The measure `µ` of
Eq. (4) satisfies `Var_µ[f] ≤ ∫ ‖∇_{Sⁿ⁻¹} f‖² dµ` for every `f ∈ C²(Sⁿ⁻¹)`. -/
theorem corollary_3_6 {n : ℕ} (hn : 3 ≤ n) (K : Fin (n - 3) → Set (E n))
    (hK : ∀ i, IsConvexBody (K i))
    (hsmooth : ∀ i, ContDiffOn ℝ ∞ (supportFunction (K i)) {0}ᶜ)
    (hpd : ∀ i, ∀ θ ∈ unitSphere n, (restrictedHessian (supportFunction (K i)) θ).PosDef)
    (f : E n → ℝ) (hf : IsC2OnSphere f) :
    ProbabilityTheory.variance (fun θ : Sph n => f θ) (muMeasure K) ≤
      ∫ θ : Sph n, ‖sphGrad f (θ : E n)‖ ^ 2 ∂(muMeasure K) := by sorry

end MixedVolFPRAS.Main
