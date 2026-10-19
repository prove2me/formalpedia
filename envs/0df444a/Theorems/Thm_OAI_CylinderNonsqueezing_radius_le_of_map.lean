-- Prove2me | Theorems.Thm_OAI_CylinderNonsqueezing_radius_le_of_map
-- name    : OAI.CylinderNonsqueezing.radius_le_of_map
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:06.777079+00:00
-- url     : https://prove2.me/theorems/79510333-dee3-45ad-9c77-b507617ecb92
-- title:
--   Gromov's non-squeezing theorem for bounded smooth symplectic embeddings of a ball into a cylinder in ℂⁿ
-- statement:
--   Let $\kappa$ be a finite type with decidable equality and $V = \mathbb C^\kappa$ (`Vector κ`, the Euclidean space `EuclideanSpace ℂ κ`), with the standard symplectic form $\omega(v, w) = \langle i v, w \rangle_{\mathbb R}$ (`ComplexSymplectic.form`, the real inner product of $i v$ and $w$). A real-linear map $A : V \to V$ preserves $\omega$ (`ComplexSymplectic.Preserves A`) if $\omega(Av, Aw) = \omega(v, w)$ for all $v, w$. For $L \in \mathbb R$ let $B_L = \{z \in V : \|z\|^2 < L\}$ (`PushedBall.domain L`), the open ball of squared radius $L$.
--
--   **Statement.** Let $j_0 \in \kappa$ and let $L, R, M$ be real numbers with $L > 0$, $R \ge 0$ and $M \ge 0$. Let $f : V \to V$ be a map that is $C^\infty$ on $B_L$, injective on $B_L$, and whose derivative preserves $\omega$ at every point of $B_L$. If $\|f(z)\|^2 \le M$ and $|f(z)_{j_0}|^2 \le R$ for every $z \in B_L$, that is, $f$ maps $B_L$ into a bounded part of the cylinder $\{w : |w_{j_0}|^2 \le R\}$, then
--   $$L \le R.$$
--
--   This is Gromov's non-squeezing theorem in $\mathbb C^\kappa$: a ball of squared radius $L$ embeds symplectically into a cylinder of squared radius $R$ over one complex coordinate only if $L \le R$. This form adds the hypothesis that the image is bounded ($\|f\|^2 \le M$ on $B_L$).
--
--   Lean: `OAI.CylinderNonsqueezing.radius_le_of_map`, OpenAI's theorem of that name (in `lean/OAI/Geometry/PolarProducts/UpperBound.lean`). `Vector`, `PushedBall.domain`, `ComplexSymplectic.form` and `ComplexSymplectic.Preserves` come from the definitions bundle `OAIQWSP000` of this split.
-- source:
--   OpenAI, Symplectic Balls in Symmetric Polar Products, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 087; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PolarProducts/UpperBound.lean (declaration OAI.CylinderNonsqueezing.radius_le_of_map)

import Mathlib
import Definitions.Def_OAIQWSP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace CylinderNonsqueezing
noncomputable section
open Set
open scoped ContDiff
open FourierPolynomial
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem radius_le_of_map (j₀ : κ) {L R M : ℝ} (hL : 0 < L) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (f : Vector κ → Vector κ) (hf : ContDiffOn ℝ ∞ f (PushedBall.domain L))
    (hi : InjOn f (PushedBall.domain L))
    (hω : ∀ z ∈ PushedBall.domain L, ComplexSymplectic.Preserves (fderiv ℝ f z))
    (hbounded : ∀ z ∈ PushedBall.domain L, ‖f z‖^2 ≤ M)
    (hcylinder : ∀ z ∈ PushedBall.domain L, ‖f z j₀‖^2 ≤ R) : L ≤ R := by
  sorry

end
end CylinderNonsqueezing
end

end OAI
end
