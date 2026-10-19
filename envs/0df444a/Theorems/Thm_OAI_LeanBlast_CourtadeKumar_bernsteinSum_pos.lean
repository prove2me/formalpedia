-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_bernsteinSum_pos
-- name    : OAI.LeanBlast.CourtadeKumar.bernsteinSum_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:57:23.865975+00:00
-- url     : https://prove2.me/theorems/b62e90e3-907c-4670-8723-db2a617d7c13
-- title:
--   A polynomial with positive Bernstein coefficients is positive on $[0,1]$
-- statement:
--   Let $d\in\mathbb{N}$ and $B_0,\dots,B_d>0$. Then for every $t\in[0,1]$,
--   $$
--   \sum_{i=0}^dB_i\binom{d}{i}t^i(1-t)^{d-i}>0 .
--   $$
--
--   This is the certificate principle: rewriting a polynomial in the Bernstein basis of an interval and checking that all coefficients are positive proves positivity on the interval by finite exact arithmetic.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/CurvatureCertificates.lean#L16-L33

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators

theorem OAI.LeanBlast.CourtadeKumar.bernsteinSum_pos (d : ℕ) (B : Fin (d + 1) → ℝ)
    (hB : ∀ i, 0 < B i) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    0 < bernsteinSum d B t := by sorry
