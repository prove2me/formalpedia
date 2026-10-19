-- Prove2me | Theorems.Thm_OAI_Moser_compactlySupported_deformation
-- name    : OAI.Moser.compactlySupported_deformation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:07.925582+00:00
-- url     : https://prove2.me/theorems/5e7a5167-763c-45f4-a2c9-fd1478c12c99
-- title:
--   Moser's trick — a closed nondegenerate two-form perturbed by an exact compactly supported form is pulled back to itself by a compactly supported diffeomorphism
-- statement:
--   Let $E$ be a complete, proper real normed space (Lean: `NormedAddCommGroup E`, `NormedSpace ℝ E`, `CompleteSpace E`, `ProperSpace E`). A two-tensor on $E$ is a continuous bilinear form, `TwoTensor E` $= E \to_L E \to_L \mathbb R$. For a map $\gamma : E \to (E \to_L \mathbb R)$ (a one-form), its exterior derivative is the two-tensor field `exteriorD γ x` $: (a, b) \mapsto D\gamma(x)(a)(b) - D\gamma(x)(b)(a)$.
--
--   **Statement.** Let $U \subseteq E$ be open, $W : E \to$ `TwoTensor E` and $\gamma : E \to (E \to_L \mathbb R)$, and assume:
--   - $W$ is $C^\infty$ at every point of $U$;
--   - $W$ is skew on $U$: $W_x(a, b) = -W_x(b, a)$ for $x \in U$;
--   - $W$ is closed on $U$: $DW(x)(a)(b)(c) + DW(x)(b)(c)(a) + DW(x)(c)(a)(b) = 0$ for $x \in U$ and all $a, b, c$;
--   - $\gamma$ is $C^\infty$, has compact support, and its topological support lies in $U$;
--   - for every $x \in U$ and $s \in [0, 1]$, the two-tensor $W_x + s\,$`exteriorD γ x` is invertible (Mathlib's `IsInvertible`, as a continuous linear map $E \to (E \to_L \mathbb R)$).
--
--   Then there is a homeomorphism $F : E \to E$ such that $F$ and $F^{-1}$ are $C^\infty$; $F(x) = x$ for $x \notin U$; $F(x) \in U$ if and only if $x \in U$; and for every $x \in U$ and all $a, b \in E$,
--   $$\bigl(W_{F(x)} + \texttt{exteriorD}\ \gamma\ (F(x))\bigr)\bigl(DF(x)\,a,\ DF(x)\,b\bigr) \;=\; W_x(a, b),$$
--   that is, $F$ pulls $W + d\gamma$ back to $W$ on $U$.
--
--   This is Moser's trick (Moser's deformation argument) for a compactly supported exact perturbation of a closed nondegenerate two-form.
--
--   Lean: `OAI.Moser.compactlySupported_deformation`, OpenAI's theorem of that name (in `lean/OAI/Geometry/PolarProducts/MoserFlow.lean`). `TwoTensor` and `exteriorD` come from the definitions bundle `OAIQWSP000` of this split.
-- source:
--   OpenAI, Symplectic Balls in Symmetric Polar Products, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 087; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PolarProducts/MoserFlow.lean (declaration OAI.Moser.compactlySupported_deformation)

import Mathlib
import Definitions.Def_OAIQWSP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u25 u26

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff

open Set Filter Function
open scoped Topology ContDiff

namespace Moser

open Set Filter Function TensorCalculus SmoothODE
open scoped Topology ContDiff NNReal

variable {E : Type u26} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [ProperSpace E]

noncomputable section

theorem compactlySupported_deformation {U : Set E} (hU : IsOpen U)
    {W : E → TwoTensor E} {γ : E → E →L[ℝ] ℝ}
    (hW : ∀ x ∈ U, ContDiffAt ℝ ∞ W x)
    (hsk : ∀ x ∈ U, ∀ a b, W x a b = -W x b a)
    (hclosed : ∀ x ∈ U, ∀ a b c,
      fderiv ℝ W x a b c + fderiv ℝ W x b c a + fderiv ℝ W x c a b = 0)
    (hγ : ContDiff ℝ ∞ γ) (hcγ : HasCompactSupport γ) (hs : tsupport γ ⊆ U)
    (hi : ∀ x ∈ U, ∀ s ∈ Icc (0 : ℝ) 1, (W x + s • exteriorD γ x).IsInvertible) :
    ∃ F : E ≃ₜ E, ContDiff ℝ ∞ (F : E → E) ∧ ContDiff ℝ ∞ (F.symm : E → E) ∧
      (∀ x, x ∉ U → F x = x) ∧ (∀ x, F x ∈ U ↔ x ∈ U) ∧
      ∀ x ∈ U, ∀ a b,
        (W (F x) + exteriorD γ (F x)) (fderiv ℝ (F : E → E) x a)
          (fderiv ℝ (F : E → E) x b) = W x a b := by
  sorry

end
end Moser

end LowerBoundInline

end OAI
end
