-- Prove2me | Theorems.Thm_Matrix_UnitaryGroup_fsMeasure_smul_invariant
-- name    : Matrix.UnitaryGroup.fsMeasure_smul_invariant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T11:56:53.703575+00:00
-- url     : https://prove2.me/theorems/eca75ad8-4ba0-4f16-8a92-27430abd0a03
-- title:
--   Unitary Group: fs Measure smul invariant
-- statement:
--   **U(N)-invariance of the Fubini–Study measure.** For any unitary
--   `U'`, pushing forward `fsMeasure p₀` by the action of `U'`
--   yields the same measure.
--
--   Proof via the chain:
--   1. unfold `fsMeasure` to expose `(orbitMap p₀).map unitaryHaarProb`;
--   2. compose maps via `Measure.map_map` to push `U' • ·` through the orbit map;
--   3. use `smul_comp_orbitMap` to re-express the composition as
--      `orbitMap p₀ ∘ (U' * ·)`;
--   4. push the multiplication-by-`U'` map back inside via `Measure.map_map`;
--   5. invoke `unitaryHaarProb`'s left-invariance (`IsMulLeftInvariant`,
--      inherited from `unitaryHaarProb_isHaarMeasure`) to kill the
--      inner pushforward.
--
--   Source: https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudy.lean#L136-L148
-- source:
--   https://github.com/zblore/born-volume-lean/blob/f010a36f123a02b04c9fa52bc0a7fb1a4188ef99/BornVolumeLean/LinearAlgebra/Projectivization/FubiniStudy.lean#L136-L148

module
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_Unitary
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_MeasureSpace
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Matrix_UnitaryHaar
public import Mathlib.Topology.Instances.Matrix
public import Definitions.Def_BornVolumeLean_LinearAlgebra_Projectivization_FubiniStudy
set_option autoImplicit false
@[expose] public section
public section
open MeasureTheory Matrix
open scoped LinearAlgebra.Projectivization
open Matrix Matrix.UnitaryGroup
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem Matrix.UnitaryGroup.fsMeasure_smul_invariant
    (U' : Matrix.unitaryGroup ι ℂ)
    (p₀ : ℙ ℂ (EuclideanSpace ℂ ι)) :
    Measure.map (fun p => U' • p) (fsMeasure p₀)
      = fsMeasure p₀ := by sorry
