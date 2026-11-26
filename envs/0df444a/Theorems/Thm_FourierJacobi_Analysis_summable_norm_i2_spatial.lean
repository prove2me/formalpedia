-- Prove2me | Theorems.Thm_FourierJacobi_Analysis_summable_norm_i2_spatial
-- name    : FourierJacobi.Analysis.summable_norm_i2_spatial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:17:13.75737+00:00
-- url     : https://prove2.me/theorems/d356c2ed-7c29-43a1-8962-4624cfb5db8f
-- title:
--   Analysis: summable norm i2 spatial
-- statement:
--   The Analysis construction uses the summable norm i2 spatial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L130-L158
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Analysis/I2Assembly.lean#L130-L158

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

theorem FourierJacobi.Analysis.summable_norm_i2_spatial (q t d U V T : ℂ) (ν : Fin 25)
    (h : GeometricRange t d U V T) :
    Summable (fun p : I2SpatialRow ν => ‖i2SpatialTerm q t d U V T ν p.val‖) := by sorry
