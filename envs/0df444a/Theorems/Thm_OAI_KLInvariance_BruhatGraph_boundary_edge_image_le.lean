-- Prove2me | Theorems.Thm_OAI_KLInvariance_BruhatGraph_boundary_edge_image_le
-- name    : OAI.KLInvariance.BruhatGraph.boundary_edge_image_le
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T05:58:28.890558+00:00
-- url     : https://prove2.me/theorems/c1596ee3-95e5-4cd8-800c-1c0ee403a647
-- title:
--   OAI.KLInvariance.BruhatGraph.boundary_edge_image_le: intermediate lemma from OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.KLInvariance.combinatorial_invariance`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168)*, OpenAI Math Release, September 24, 2026, result family 168, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.KLInvariance.BruhatGraph.boundary_edge_image_le` of [lean/OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.KLInvariance.BruhatGraph`, with `open Module TitsSpace MomentGraph MomentGraph.Sheaf`):
--
--   ```lean
--    theorem boundary_edge_image_le (e : Edge cs 1 b)
--       (hx : BruhatLE cs u (source cs 1 b e).val)
--       [Module.Free (MvPolynomial σ ℝ)
--         ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.upwardSubmodule
--           (target cs 1 b e) {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)})] :
--       let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
--       let T := ambientLater φ (mappedEdgeRoot φ e hx)
--       (D.upwardKernel (source cs 1 b e) {f | f.val ∈ T}).map (D.lower e) ≤
--         ((D.upwardKernel (target cs 1 b e) {f | f.val ∈ T}).map (D.upper e)).map
--           (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e)
--             (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.KLInvariance.bruhat_refl`, `OAI.KLInvariance.BruhatGraph.Edge`, `OAI.KLInvariance.BruhatGraph.graph`, `OAI.KLInvariance.BruhatGraph.polynomialLabel`, `OAI.KLInvariance.BruhatGraph.root`, `OAI.KLInvariance.BruhatGraph.source`, `OAI.KLInvariance.BruhatGraph.target`, `OAI.KLInvariance.Graded.polynomialGrading`, `OAI.KLInvariance.Graded.polynomialGrading_decomposition`, `OAI.KLInvariance.Graded.polynomialGrading_monoid`, `OAI.KLInvariance.Graded.polynomialGrading_negative`, `OAI.KLInvariance.MomentGraph.Sheaf`, `OAI.KLInvariance.TitsSpace.Extended`, `OAI.KLInvariance.TitsSpace.form`, `OAI.KLInvariance.Graded.ModuleData.instAddCommGroupCarrierObj`, `OAI.KLInvariance.Graded.ModuleData`, `OAI.KLInvariance.MomentGraph.BoundarySheaf`, `OAI.KLInvariance.MomentGraph.GradedSheaf.forget`, `OAI.KLInvariance.MomentGraph.GradedSheaf` and `OAI.KLInvariance.MomentGraph.OrderedGraph` (definitions bundle `OAIQ124K000` of this split); `OAI.KLInvariance.one_bruhat`, `OAI.KLInvariance.BruhatGraph.boundarySheaf`, `OAI.KLInvariance.MomentGraph.GradedSheaf.upwardSubmodule`, `OAI.KLInvariance.MomentGraph.Sheaf.Outgoing` and `OAI.KLInvariance.MomentGraph.Sheaf.upwardKernel` (definitions bundle `OAIQ124K004` of this split); `OAI.KLInvariance.BruhatGraph.edgeFactorLift` (definitions bundle `OAIQ124K009` of this split); `OAI.KLInvariance.BruhatGraph.mappedEdgeRoot` (definitions bundle `OAIQ124K011` of this split); `OAI.KLInvariance.BruhatGraph.ambientLater` (definitions bundle `OAIQ124K015` of this split); `OAI.KLInvariance.BruhatLE`, `OAI.KLInvariance.Interval` and `OAI.KLInvariance.intervalOrder` (the published bundle `Def_KLInvariance`).
--
--   **Used by.** The proofs of `OAI.KLInvariance.BruhatGraph.actual_comparison_of_upper_freeness` and `OAI.KLInvariance.BruhatGraph.actual_freeSuffixes_of_rTilde_eq` of this split import it.
-- source:
--   OpenAI, Combinatorial invariance of Kazhdan–Lusztig polynomials (result family 168), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 168; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Combinatorial-Invariance-of-Kazhdan-Lusztig-Polynomials-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RepresentationTheory/KazhdanLusztig/TerminalKernels.lean (declaration OAI.KLInvariance.BruhatGraph.boundary_edge_image_le)

import Mathlib
import Definitions.Def_KLInvariance
import Definitions.Def_OAIQ124K015

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace KLInvariance.BruhatGraph
open Module TitsSpace MomentGraph MomentGraph.Sheaf
universe u v us u' v'
variable {I : Type u} [Fintype I] {M : CoxeterMatrix I}
  {W : Type v} [Group W] {cs : CoxeterSystem M W}
  {σ : Type (max us v)} [Fintype σ] (basis : Basis σ ℝ (Extended M))
  {I' : Type u'} [Fintype I'] {M' : CoxeterMatrix I'}
  {W' : Type v'} [Group W'] {cs' : CoxeterSystem M' W'}
  {u b : W} {u' b' : W'}
  (φ : Interval cs u b ≃o Interval cs' u' b')
noncomputable section

 theorem boundary_edge_image_le (e : Edge cs 1 b)
    (hx : BruhatLE cs u (source cs 1 b e).val)
    [Module.Free (MvPolynomial σ ℝ)
      ((boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.upwardSubmodule
        (target cs 1 b e) {f | f.val ∈ ambientLater φ (mappedEdgeRoot φ e hx)})] :
    let D := (boundarySheaf cs 1 b basis (one_bruhat cs b)).sheaf.forget
    let T := ambientLater φ (mappedEdgeRoot φ e hx)
    (D.upwardKernel (source cs 1 b e) {f | f.val ∈ T}).map (D.lower e) ≤
      ((D.upwardKernel (target cs 1 b e) {f | f.val ∈ T}).map (D.upper e)).map
        (LinearMap.lsmul (MvPolynomial σ ℝ) (D.edge e)
          (edgeFactorLift cs basis (source cs 1 b e).val (root cs 1 b e))) := by
  sorry

end
end KLInvariance.BruhatGraph

end

end OAI
end
