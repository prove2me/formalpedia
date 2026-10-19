-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_weighted_series_gap_hasSum
-- name    : OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:25:19.313073+00:00
-- url     : https://prove2.me/theorems/44b71296-ec35-412e-a2f7-9d967f9134b6
-- title:
--   Series expansion of a weighted Jensen gap
-- statement:
--   Let $\iota$ be a finite index set, $c:\mathbb{N}\to\mathbb{R}$, $p:\mathbb{N}\to\mathbb{N}$ and $F:\mathbb{R}\to\mathbb{R}$. Let $w,x:\iota\to\mathbb{R}$ and $y\in\mathbb{R}$, and suppose
--   $$
--   F(x_i)=\sum_jc_j\,x_i^{p_j}\quad(\text{each }i),\qquad F(y)=\sum_jc_j\,y^{p_j}
--   $$
--   as convergent series. Then
--   $$
--   \sum_j2c_j\Bigl(\sum_iw_ix_i^{p_j}-y^{p_j}\Bigr)=2\Bigl(\sum_iw_iF(x_i)-F(y)\Bigr),
--   $$
--   the left side converging.
--
--   Applied to $F=\psi$, with $c_j$ its positive coefficients and $p_j=2j+2$, this writes a Jensen gap of $\psi$ as a series of power-mean gaps, each nonnegative when $y$ is the weighted mean.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/JensenGaps.lean#L101-L119

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Attainment
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_ComparisonEstimates
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LambdaScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_JensenGaps

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
universe u
variable {ι : Type u} [Fintype ι]

theorem OAI.LeanBlast.CourtadeKumar.weighted_series_gap_hasSum (c : ℕ → ℝ) (p : ℕ → ℕ) (F : ℝ → ℝ)
    (w x : ι → ℝ) (y : ℝ)
    (hx : ∀ i, HasSum (fun j => c j * (x i) ^ (p j)) (F (x i)))
    (hy : HasSum (fun j => c j * y ^ (p j)) (F y)) :
    HasSum (fun j => 2 * c j * ((∑ i, w i * (x i) ^ (p j)) - y ^ (p j)))
      (2 * ((∑ i, w i * F (x i)) - F y)) := by sorry
