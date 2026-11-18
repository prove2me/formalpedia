-- Prove2me | Theorems.Thm_OAI_ElementaryPositivity_TriangularDynamics_graph_common_history
-- name    : OAI.ElementaryPositivity.TriangularDynamics.graph_common_history
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-17T18:36:39.204434+00:00
-- url     : https://prove2.me/theorems/71b2bf51-5b1f-438d-864c-29983adba0df
-- title:
--   OAI.ElementaryPositivity.TriangularDynamics.graph_common_history: intermediate lemma from OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.elementaryPositivityWitness_exists`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Elementary Positivity of Chromatic Quasisymmetric Functions*, OpenAI Math Release, September 24, 2026, result family 169, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ElementaryPositivity.TriangularDynamics.graph_common_history` of [lean/OAI/Combinatorics/Chromatic/Histories/GraphCommonHistory.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/GraphCommonHistory.lean) at commit 7ef5c0c.
--
--   **The statement**, as published (namespace `OAI.ElementaryPositivity.TriangularDynamics`, with `open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint`, `open scoped BigOperators`, `open Classical`, and `variable {n D:ℕ}`):
--
--   ```lean
--   theorem graph_common_history (G:NaturalUnitIntervalGraph n) :
--       ∃D:ℕ,∃p:LocalHistoryFormula (Extended (Vertex D (Cell D)))
--         ((Vertex D (Cell D) → ℝ) × (Vertex D (Cell D) → ℝ)),
--         p.Positive (extendedOmega D) (extendedRoots D) extendedCast
--           (simpleTotalTransport (extendedOmega D) (extendedRoots D)) ∧
--         ∀(r:ℕ) (a:Fin r →₀ ℕ),a.degree=n →
--           (∑κ:Fin n → Fin r,
--             if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
--               (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
--           ∑l:{l:p.Leaf // AnchoredLeaf n p l},
--             p.leafWeight (extendedOmega D) (extendedRoots D) extendedCast
--               (simpleTotalTransport (extendedOmega D) (extendedRoots D)) l.val *
--             (∏i:Fin (D+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ) (leafProfile n p l i)).coeff a
--   ```
--
--   **In words.** For a natural unit interval graph `G` on `n` vertices, the statement says that there exist `D : ℕ` and a local history formula `p`, which is `Positive` for `extendedOmega D`, `extendedRoots D`, `extendedCast` and `simpleTotalTransport (extendedOmega D) (extendedRoots D)`, and such that for every `r : ℕ` and every `a : Fin r →₀ ℕ` of degree `n`, a coloring sum over the proper colorings `κ` of `G` with color class sizes `a` equals a sum over the anchored leaves `l` of `p` of `p.leafWeight` times the coefficient of `a` in a product of elementary symmetric polynomials.
--
--   **Definitions.** The statement uses `NaturalUnitIntervalGraph`, `LocalHistoryFormula`, `extendedOmega`, `extendedRoots`, `simpleTotalTransport`, `AnchoredLeaf` and `leafProfile`, written in the definitions bundles `OAIQ368Chrom054` and `OAIQ368Chrom058` of this split and in the shared definitions file Def_ElementaryPositivity.
--
--   **Used by.** Its proof file imports the published statements `OAI.ElementaryPositivity.QuantumTorus.positive_sections`, `OAI.ElementaryPositivity.QuantumTorus.section_line_program`, `OAI.ElementaryPositivity.QuantumTorus.thetaValue_positive`, `OAI.ElementaryPositivity.QuantumTorus.wall_joint_induction`, `OAI.ElementaryPositivity.TriangularDynamics.genuine_history_cut_deficit`, `OAI.ElementaryPositivity.TriangularDynamics.triangularPureIncoming_delta` and `OAI.ElementaryPositivity.TriangularDynamics.triangularPure_equal` of this split.
-- source:
--   OpenAI, Elementary Positivity of Chromatic Quasisymmetric Functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 169; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Elementary-Positivity-of-Chromatic-Quasisymmetric-Functions-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Combinatorics/Chromatic/Histories/GraphCommonHistory.lean (declaration OAI.ElementaryPositivity.TriangularDynamics.graph_common_history)

import Mathlib
import Definitions.Def_ElementaryPositivity
import Definitions.Def_OAIQ368Chrom058

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace ElementaryPositivity.TriangularDynamics
open QuantumTorus WallUnits LatticeExtension LatticeRealization PowerSeries PowerSeriesAdjoint
open scoped BigOperators
open Classical
noncomputable section
variable {n D:ℕ}

theorem graph_common_history (G:NaturalUnitIntervalGraph n) :
    ∃D:ℕ,∃p:LocalHistoryFormula (Extended (Vertex D (Cell D)))
      ((Vertex D (Cell D) → ℝ) × (Vertex D (Cell D) → ℝ)),
      p.Positive (extendedOmega D) (extendedRoots D) extendedCast
        (simpleTotalTransport (extendedOmega D) (extendedRoots D)) ∧
      ∀(r:ℕ) (a:Fin r →₀ ℕ),a.degree=n →
        (∑κ:Fin n → Fin r,
          if G.Proper κ ∧ (∀i,(Finset.univ.filter (fun j=>κ j=i)).card=a i) then
            (↑(LaurentRay.vUnit^(2*(G.coloringInversions κ:ℤ)-(G.edgeCount:ℤ))):LaurentSeries ℚ) else 0)=
        ∑l:{l:p.Leaf // AnchoredLeaf n p l},
          p.leafWeight (extendedOmega D) (extendedRoots D) extendedCast
            (simpleTotalTransport (extendedOmega D) (extendedRoots D)) l.val *
          (∏i:Fin (D+1),MvPolynomial.esymm (Fin r) (LaurentSeries ℚ) (leafProfile n p l i)).coeff a := by
  sorry
end
end ElementaryPositivity.TriangularDynamics

end

end OAI
end
