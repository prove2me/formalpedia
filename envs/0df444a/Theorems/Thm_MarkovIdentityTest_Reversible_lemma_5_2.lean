-- Prove2me | Theorems.Thm_MarkovIdentityTest_Reversible_lemma_5_2
-- name    : MarkovIdentityTest.Reversible.lemma_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:39:17.918894+00:00
-- url     : https://prove2.me/theorems/f477768a-d39d-4afd-89ad-3d7b7fe79f76
-- title:
--   Lemma 5.2 — two different rows: $|\mathbb E[W_iW_j]|\le 4\ell^2$
-- statement:
--   Let $Q$ be stochastic, $x$ any initial state and $T$ an independent positive geometric time of mean $M\ge1$. Let $i\ne j$ be two states with destination features $\phi$ (for row $i$) and $\psi$ (for row $j$), centred under $Q_i$ and $Q_j$ respectively, whose covariances are bounded by $\ell I$ ($\ell\ge0$). Let $W_i,W_j$ be their retained-row scores on the path observed up to $T$. Then $W_iW_j$ is integrable and
--   $$|\mathbb E[W_iW_j]|\le4\ell^2 .$$
--   This controls the cross terms in the second moment of the total score, which do not vanish because one trajectory decides whether both rows are visited.
--
--   Differences from the source:
--
--   - reading: ℓ, the covariance bound → hypothesis 0 ≤ ℓ; reason: implicit in the paper; Σ ⪯ ℓI forces it whenever the feature dimension is ≥ 1
--   - encoding: features centred under the row law (standing assumption of §5.2.1) → ∑_y Q_iy ϕ(y) = 0, ∑_y Q_jy ψ(y) = 0, separate dimensions D₁, D₂; reason: the rows' original laws are Q_i, Q_j
--   - encoding: E at the geometric time → series over t with absolute convergence asserted; M ∈ ℝ, M ≥ 1; reason: same law; integrability rules out a default value 0
-- source:
--   Jianhao Jia, Identity Testing of Markov Chains from a Single Trajectory, STOC 2027 submission (manuscript sha256 cf0995fc…), p. 27, Lemma 5.2

import Mathlib
import Definitions.Def_CEPolytopeHard_IsStochastic
import Definitions.Def_MarkovIdentityTest_Reversible_Trajectory
import Definitions.Def_MarkovIdentityTest_Reversible_StoppedRow

set_option autoImplicit false

open CEPolytopeHard

namespace MarkovIdentityTest.Reversible

/-- Lemma 5.2 (Jia, p. 27 / PDF 29): for the chain `Q` from any `x` at an independent positive
geometric time of mean `M`, two distinct rows `i ≠ j` whose destination features are centred
under `Qᵢ`, `Qⱼ` with covariance `⪯ ℓI` have `|E[Wᵢ Wⱼ]| ≤ 4ℓ²`. -/
theorem lemma_5_2 {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : IsStochastic Q) (M : ℝ)
    (hM : 1 ≤ M) (x i j : Fin n) (hij : i ≠ j) {D₁ D₂ : ℕ}
    (ϕ : Fin n → Fin D₁ → ℝ) (ψ : Fin n → Fin D₂ → ℝ) (ℓ : ℝ) (hℓ : 0 ≤ ℓ)
    (hϕmean : ∑ y, Q i y • ϕ y = 0)
    (hϕcov : ∀ u : Fin D₁ → ℝ,
      dotProduct u (Matrix.mulVec (featureCov (Q i) ϕ) u) ≤ ℓ * dotProduct u u)
    (hψmean : ∑ y, Q j y • ψ y = 0)
    (hψcov : ∀ u : Fin D₂ → ℝ,
      dotProduct u (Matrix.mulVec (featureCov (Q j) ψ) u) ≤ ℓ * dotProduct u u) :
    GeomIntegrable M Q x (fun _ ω => chainRowScore ϕ i ω * chainRowScore ψ j ω) ∧
      |geomExp M Q x (fun _ ω => chainRowScore ϕ i ω * chainRowScore ψ j ω)| ≤ 4 * ℓ ^ 2 := by sorry

end MarkovIdentityTest.Reversible
