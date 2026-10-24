-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_normalPotentials_uniform_pinching
-- name    : OAI.PinchedHartogs.normalPotentials_uniform_pinching
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:07:19.664669+00:00
-- url     : https://prove2.me/theorems/fcb14787-5dcc-4f58-bd22-7281fc874697
-- title:
--   Uniform negative pinching for the normalized Hartogs potentials (OpenAI pinched Kähler threefold, Lemma 9.2)
-- statement:
--   The notation is that of the published statements `OAI.PinchedHartogs.normalCurvature_model` and `OAI.PinchedHartogs.normalErrors_bounds` (`normalLogWeight`, `normalPotential`, `liftedThird`, `liftedFourth`, `form`, `euclidean`; definitions bundle `OAIQWPH001`). From the published bundle `Def_PinchedKahler`: `Ambient` is $\mathbb C^3 = \mathbb C^2 \times \mathbb C$, `complexHessian` the complex Hessian on it, and `sectional g p u v` the sectional curvature of the Kähler form $g$ at $p$ on the real two-plane spanned by $u, v$. `metricThreshold c C` is an explicit threshold $\lambda_0(c, C) > 0$ (definitions bundle `OAIQWPH001`).
--
--   **Statement.** Let $0 < c \le C$ and $\lambda \ge$ `metricThreshold c C`. There are $0 < a \le b$ such that for every $f : \mathbb C^2 \to \mathbb R$ smooth at $0$ whose complex Hessian $h$ at $0$ satisfies $c|u|^2 \le h(u,u) \le C|u|^2$ and whose horizontal third and fourth derivatives at $0$ have norm at most $C$, every $w \in \mathbb C$ with `normalLogWeight f w (0,w)` $< 0$, and every real-linearly independent $u, v \in \mathbb C^3$,
--   $$-b \;\le\; \mathrm{sectional}\bigl(\mathrm{complexHessian}(\mathrm{normalPotential}\,f\,\lambda\,w)\bigr)\,(0, w)\,u\,v \;\le\; -a.$$
--
--   This is Lemma 9.2 of the paper, applied to the normalized potentials: for $\lambda$ beyond a threshold depending only on $c$ and $C$, the sectional curvatures are pinched between two negative constants independent of $f$ and $w$.
--
--   Lean: `OAI.PinchedHartogs.normalPotentials_uniform_pinching`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/HartogsFrame.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Lemma 9.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/HartogsFrame.lean (declaration OAI.PinchedHartogs.normalPotentials_uniform_pinching)

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

lemma normalPotentials_uniform_pinching {c C lam : ℝ} (hc : 0 < c) (hC : c ≤ C)
    (hlam : metricThreshold c C ≤ lam) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧
      ∀ (f : Base → ℝ) (hf : ContDiffAt ℝ ∞ f 0),
      (∀ u, c * euclidean.q u ≤ (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u) →
      (∀ u, (form (baseHessian f 0)
        (baseHessian_isHermitian (hf.of_le (WithTop.coe_le_coe.mpr le_top)))).q u ≤ C * euclidean.q u) →
      (∀ i j k : Fin 2, ‖liftedThird f (0,0) i.castSucc j.castSucc k.castSucc‖ ≤ C) →
      (∀ i j k l : Fin 2, ‖liftedFourth f (0,0) i.castSucc j.castSucc k.castSucc l.castSucc‖ ≤ C) →
      ∀ w : ℂ, normalLogWeight f w (0,w) < 0 →
      ∀ u v : Ambient, LinearIndependent ℝ ![u,v] →
        -b ≤ sectional (complexHessian (normalPotential f lam w)) (0,w) u v ∧
          sectional (complexHessian (normalPotential f lam w)) (0,w) u v ≤ -a := by
  sorry

end PinchedHartogs

end

end OAI
end
