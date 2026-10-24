-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_normalCurvature_model
-- name    : OAI.PinchedHartogs.normalCurvature_model
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:06:59.044427+00:00
-- url     : https://prove2.me/theorems/185bf084-274a-46aa-ab36-41150294feab
-- title:
--   Curvature model of the normalized Hartogs potential (OpenAI pinched Kähler threefold, Proposition 8.1)
-- statement:
--   `Base` ($\mathbb C^2$), `baseHessian` (the complex Hessian on $\mathbb C^2$), `complexHessian` and `curvature` (on $\mathbb C^3 = \mathbb C^2 \times \mathbb C$) are from the published bundle `Def_PinchedKahler`. The other definitions are from the definitions bundle `OAIQWPH001` of this split, following Section 8 of the paper. For $f : \mathbb C^2 \to \mathbb R$, $\lambda \in \mathbb R$ and $w \in \mathbb C$:
--   - `normalLogWeight f w` is the gauge-normalized logarithmic weight $s(z, w') = f(z) - 2\operatorname{Re}\bigl(g(z, w') - w'\bigr)$ on $\mathbb C^2 \times \mathbb C$, where $g$ = `baseGaugePolynomial f w` is a polynomial built from the first and second jets of $f$ at $(0, w)$; and `normalPotential f λ w` is $\lambda\psi + (-\log(1 - e^{s}))$, with $\psi(z) = -\log(1-|z|^2)$;
--   - `barrierX s` is $x = e^s/(1-e^s)$, `horizontalMetric A λ x` is $G = \lambda I + xA$, and `curvatureModel A λ x T₄ T₃` is the tensor $-\lambda S_I - qS_h - S_V - (S_{D+V} - S_D - S_V) + T_4 + T_3$ of the paper's (8.4), with $q = x(1+x)$, $h = A$, $D = (1+2x)A - qAG^{-1}A$ and $S$ the symmetrized product of Hermitian forms;
--   - `normalCurvature f λ w` is the curvature tensor of the Kähler metric with potential `normalPotential f λ w` at $(0, w)$ in the frame of the paper (vertical direction rescaled by $1/\sqrt q$), and `normalError f λ w` is its difference from `curvatureModel … 0 0`; `horizontalPart j T` keeps the components with exactly $j$ horizontal indices.
--
--   **Statement.** Let $f$ be smooth at $0$, $\lambda \in \mathbb R$, $w \in \mathbb C$ with $s = $ `normalLogWeight f w (0,w)` $< 0$, and suppose $\det G \ne 0$ for $G$ = `horizontalMetric (baseHessian f 0) λ (barrierX s)`. Then
--   $$\mathrm{normalCurvature}\,f\,\lambda\,w \;=\; \mathrm{curvatureModel}\bigl(\mathrm{baseHessian}\,f\,0,\ \lambda,\ \mathrm{barrierX}\,s,\ \mathrm{horizontalPart}_4(\mathrm{normalError}),\ \mathrm{horizontalPart}_3(\mathrm{normalError})\bigr).$$
--
--   This is Proposition 8.1 of the paper: the full curvature tensor has the form (8.4), where the error tensors $T_4$, $T_3$ have exactly four and three horizontal indices.
--
--   Lean: `OAI.PinchedHartogs.normalCurvature_model`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/HartogsModelBridge.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Proposition 8.1, (8.4); Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/HartogsModelBridge.lean (declaration OAI.PinchedHartogs.normalCurvature_model)

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
open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open Complex
noncomputable section

open Set Filter Topology
open scoped ContDiff Matrix Matrix.Norms.Elementwise
namespace PinchedHartogs
open PlaneAlgebra PlaneAlgebra.MatrixAlgebra PlaneAlgebra.TensorAlgebra

lemma normalCurvature_model {f : Base → ℝ} (hf : ContDiffAt ℝ ∞ f 0)
    (lam : ℝ) (w : ℂ) (hn : normalLogWeight f w (0,w) < 0)
    (hG : (horizontalMetric (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))).det ≠ 0) :
    normalCurvature f lam w = curvatureModel (baseHessian f 0) lam (barrierX (normalLogWeight f w (0,w)))
      (horizontalPart 4 (normalError f lam w)) (horizontalPart 3 (normalError f lam w)) := by
  sorry

end PinchedHartogs

end

end OAI
end
