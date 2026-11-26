-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_bare
-- name    : FourierJacobi.Analysis.summable_norm_i2_bare
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:59.531591+00:00
-- url     : https://prove2.me/theorems/5df76eea-8711-5331-b788-5206c8558bb1
-- title:
--   Analysis: summable norm i2 bare
-- statement:
--   The Analysis construction uses the summable norm i2 bare property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L321-L331
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L321-L331

import Definitions.Def_FourierJacobi_Analysis_I2Complete
import Definitions.Def_FourierJacobi_Analysis_I2Predicates
import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Definitions.Def_FourierJacobi_Analysis_I2Assembly
set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Valuations
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem FourierJacobi.Analysis.summable_norm_i2_bare (q t d U V T : ℂ) (ν : Fin 25)
    (hq₀ : q ≠ 0) (hq₁ : q - 1 ≠ 0) (hq₂ : q - 2 ≠ 0) (hq : ‖q⁻¹‖ < 1)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2BareTerm q t d U V T ν p‖) := by sorry
