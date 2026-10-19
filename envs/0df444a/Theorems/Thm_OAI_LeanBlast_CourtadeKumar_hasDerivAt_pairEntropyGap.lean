-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_hasDerivAt_pairEntropyGap
-- name    : OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:59:15.322896+00:00
-- url     : https://prove2.me/theorems/523b7c96-7ecf-4cc7-bfcb-1878ba908bc0
-- title:
--   Derivative of the pair entropy gap
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$ and $h(v)=\log2-\psi(v)$, the entropy in nats of a random sign with mean $v$. Let
--   $$
--   \Delta(a,b)=h(a)-\frac{h(a+b)+h(a-b)}2
--   $$
--   be the pair entropy gap. If $|a|+|b|<1$, then $b\mapsto\Delta(a,b)$ is differentiable at $b$ with derivative $\frac12\bigl(\operatorname{artanh}(a+b)-\operatorname{artanh}(a-b)\bigr)$.
--
--   This derivative is the one-coordinate dissipation density.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/PairEntropy.lean#L224-L239

import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureCertificates__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_InverseScalars__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropySeries__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_MediumCurvature__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CurvatureBounds__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_LRegularity__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Rearrangement__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_SemigroupFlow__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_CubeSplits__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_PairEntropy__SoftChannel204

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar

theorem OAI.LeanBlast.CourtadeKumar.hasDerivAt_pairEntropyGap (a b : ℝ) (h : |a| + |b| < 1) :
    HasDerivAt (fun t => pairEntropyGap a t)
      ((Real.artanh (a + b) - Real.artanh (a - b)) / 2) b := by sorry
