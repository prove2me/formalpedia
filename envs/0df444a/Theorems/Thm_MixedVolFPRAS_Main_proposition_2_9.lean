-- Prove2me | Theorems.Thm_MixedVolFPRAS_Main_proposition_2_9
-- name    : MixedVolFPRAS.Main.proposition_2_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T20:30:47.508115+00:00
-- url     : https://prove2.me/theorems/453d361b-05cf-4d29-8d79-4e17591d3581
-- title:
--   Proposition 2.9 — Vₙ(K₁,…,Kₙ) = (1/n)∫ h_{K₁}·D_{n−1}(D²h_{K₂},…,D²h_{Kₙ}) dω
-- statement:
--   Let $K_1,\dots,K_n\subseteq\mathbb{R}^n$ be convex bodies whose support functions $h_{K_i}$ are twice continuously differentiable on $\mathbb{R}^n\setminus\{0\}$ and whose restricted Hessians $D^2h_{K_i}(\theta)$ are positive definite on $\theta^\perp$ for every $\theta\in S^{n-1}$. Then
--
--   $$V_n(K_1,\dots,K_n)=\frac1n\int_{S^{n-1}}h_{K_1}(\theta)\,D_{n-1}\big(D^2h_{K_2}(\theta),\dots,D^2h_{K_n}(\theta)\big)\,d\omega(\theta).$$
--
--   This classical integral formula is the bridge from mixed volumes to mixed discriminants on which the smooth-case algorithm (Theorem 3.3) rests, and it shows that the measure $\mu$ of Eq. (4) is a probability measure.
--
--   Differences from the source:
--   - encoding: $K_1,\dots,K_n$ → `1 ≤ n` is a binder, $K_1$ is `K ⟨0, _⟩` and $K_{j+2}$ is `K ⟨j + 1, _⟩`; reason: 0-based indices, and the formula needs a first body.
-- source:
--   Chen, Liu, An FPRAS for Mixed Volumes, STOC 2027 submission (manuscript sha256 0acf8d97…), p. 10, Proposition 2.9

import Mathlib
import Definitions.Def_MixedVolFPRAS_Main_MixedVolume
import Definitions.Def_MixedVolFPRAS_Main_MixedDiscriminant
import Definitions.Def_MixedVolFPRAS_Main_Sphere

namespace MixedVolFPRAS.Main

/-- **Proposition 2.9.** For convex bodies `K₁, …, Kₙ ⊆ ℝⁿ` whose support functions are `C²` on
`ℝⁿ \ {0}` with `D²h_{Kᵢ}(θ)` positive definite on `θ^⊥` for every `θ ∈ Sⁿ⁻¹`,
`Vₙ(K₁, …, Kₙ) = (1/n) ∫_{Sⁿ⁻¹} h_{K₁} · D_{n−1}(D²h_{K₂}, …, D²h_{Kₙ}) dω`.
Here `K ⟨0, _⟩` is `K₁` and `K ⟨j + 1, _⟩` is `K_{j+2}`. -/
theorem proposition_2_9 {n : ℕ} (hn : 1 ≤ n) (K : Fin n → Set (E n))
    (hK : ∀ i, IsConvexBody (K i))
    (hC2 : ∀ i, ContDiffOn ℝ 2 (supportFunction (K i)) {0}ᶜ)
    (hpd : ∀ i, ∀ θ ∈ unitSphere n, (restrictedHessian (supportFunction (K i)) θ).PosDef) :
    mixedVolume K =
      (1 / (n : ℝ)) * ∫ θ : Sph n,
        supportFunction (K ⟨0, by omega⟩) (θ : E n) *
          mixedDiscriminant (fun j : Fin (n - 1) =>
            restrictedHessian (supportFunction (K ⟨j.val + 1, by have := j.isLt; omega⟩))
              (θ : E n)) ∂(surfaceMeasure n) := by sorry

end MixedVolFPRAS.Main
