-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_concaveOn_entropy
-- name    : OAI.LeanBlast.CourtadeKumar.concaveOn_entropy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T14:55:39.48598+00:00
-- url     : https://prove2.me/theorems/1e549916-89e8-4d0e-968a-1f552bbe15e6
-- title:
--   The sign entropy is concave
-- statement:
--   Let $h(v)=\log2-\psi(v)$ with $\psi(v)=\frac{1+v}2\log(1+v)+\frac{1-v}2\log(1-v)$; this is the entropy in nats of a random sign with mean $v$. Then $h$ is concave on $[-1,1]$:
--   $$
--   h(av+bw)\ge a\,h(v)+b\,h(w)\qquad(v,w\in[-1,1],\ a,b\ge0,\ a+b=1).
--   $$
--
--   Equivalently $\psi$ is convex on $[-1,1]$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/EntropyScalars.lean#L95-L107

import Mathlib
import Definitions.Def_SoftChannel204
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Model
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic__SoftChannel204
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars__SoftChannel204

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open Set Filter
open scoped Topology

theorem OAI.LeanBlast.CourtadeKumar.concaveOn_entropy : ConcaveOn ℝ (Icc (-1) 1) entropy := by sorry
