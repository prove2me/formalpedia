-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_psi_symmetric_pair_mono
-- name    : OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:58:13.803617+00:00
-- url     : https://prove2.me/theorems/8de0b90a-d68d-4397-8639-be0cd1944661
-- title:
--   Symmetric pair sums of $\psi$ increase with the spread
-- statement:
--   Let $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$ and $h(v)=\log2-\psi(v)$, the entropy in nats of a random sign with mean $v$. Let $c\ge0$, $-c\le b\le c$, and $a\pm c\in[-1,1]$. Then
--   $$
--   \psi(a+b)+\psi(a-b)\le\psi(a+c)+\psi(a-c).
--   $$
--
--   So spreading a symmetric pair of means apart increases the sum of $\psi$, equivalently decreases the average entropy.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean#L268-L296

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.psi_symmetric_pair_mono (a b c : ℝ) (hc : 0 ≤ c)
    (hb : -c ≤ b ∧ b ≤ c)
    (hminus : a - c ∈ Set.Icc (-1 : ℝ) 1)
    (hplus : a + c ∈ Set.Icc (-1 : ℝ) 1) :
    psi (a + b) + psi (a - b) ≤ psi (a + c) + psi (a - c) := by sorry
