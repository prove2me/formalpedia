-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_normalErrors_bounds
-- name    : OAI.PinchedHartogs.normalErrors_bounds
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:06:44.263673+00:00
-- url     : https://prove2.me/theorems/80adf089-899c-4a3e-8e8c-68dc48621879
-- title:
--   Bounds for the curvature error tensors of the normalized Hartogs potential (OpenAI pinched Kähler threefold, Section 9)
-- statement:
--   The notation is that of the published statement `OAI.PinchedHartogs.normalCurvature_model` (`normalLogWeight`, `normalError`, `horizontalPart`, `barrierX`; definitions bundle `OAIQWPH001`, with `baseHessian` from the published bundle `Def_PinchedKahler`). In addition: `barrierQ s` $= x(1+x)$ with $x$ = `barrierX s`; `form A` is the Hermitian form of a Hermitian matrix and `euclidean` the standard one; `liftedThird f q a c d` and `liftedFourth f q a b c d` are the third and fourth complex derivatives $\partial_a\partial_c\bar\partial_d f$ and $\partial_a\bar\partial_b\partial_c\bar\partial_d f$ of $f$ (lifted to $\mathbb C^3$); `componentNorm T` is the Euclidean norm of the components of a tensor.
--
--   **Statement.** Let $f$ be smooth at $0$, let $0 < c \le C$ and $\lambda > 0$, and suppose that the complex Hessian $h$ of $f$ at $0$ satisfies $c\,|u|^2 \le h(u, u) \le C\,|u|^2$, and that all horizontal third and fourth derivatives of $f$ at $0$ have norm at most $C$. Let $w \in \mathbb C$ with $s = $ `normalLogWeight f w (0,w)` $< 0$, and put $E = 9\,(C + 4C^2/c)$. Then
--   $$\|T_4\| \le E\,\mathrm{barrierX}(s), \qquad \|T_3\| \le E\,\sqrt{\mathrm{barrierQ}(s)},$$
--   where $T_j$ = `horizontalPart j (normalError f λ w)` and the norms are `componentNorm`.
--
--   These are the bounds on the error tensors $T_4$, $T_3$ of (8.4) used in Section 9 of the paper to make the errors negligible for large $\lambda$.
--
--   Lean: `OAI.PinchedHartogs.normalErrors_bounds`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/HartogsErrorBounds.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Sections 8–9; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/HartogsErrorBounds.lean (declaration OAI.PinchedHartogs.normalErrors_bounds)

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped ContDiff
open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra Matrix

lemma normalErrors_bounds {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C) (hlam : 0 < lam)
    (hl : ∀ u, c * euclidean.q u ≤ (form (baseHessian f 0)
      (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u)
    (hu : ∀ u, (form (baseHessian f 0)
      (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C * euclidean.q u)
    (hJ : ∀ a c d : Fin 2, ‖liftedThird f (0,0) a.castSucc c.castSucc d.castSucc‖ ≤ C)
    (hB : ∀ a b c d : Fin 2, ‖liftedFourth f (0,0) a.castSucc b.castSucc c.castSucc d.castSucc‖ ≤ C)
    (w : ℂ) (hn : normalLogWeight f w (0,w) < 0) :
    componentNorm (horizontalPart 4 (normalError f lam w)) ≤
      (9*(C+4*C^2/c)) * barrierX (normalLogWeight f w (0,w)) ∧
    componentNorm (horizontalPart 3 (normalError f lam w)) ≤
      (9*(C+4*C^2/c)) * Real.sqrt (barrierQ (normalLogWeight f w (0,w))) := by
  sorry

end PinchedHartogs

end

end OAI
end
