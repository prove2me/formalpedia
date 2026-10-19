-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_noiseOperator_setBit
-- name    : OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:56:42.129282+00:00
-- url     : https://prove2.me/theorems/a3da1c40-6ccb-48b5-91fe-3d3219767972
-- title:
--   Splitting the noise operator along one coordinate
-- statement:
--   On the Boolean cube $\{0,1\}^n$, $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and the noise operator with correlation $u$ is $(T_ug)(x)=\sum_yK_u(x,y)g(y)$ with $K_u(x,y)=\prod_i\frac{1\pm u}{2}$ ($+$ where $x_i=y_i$, $-$ otherwise). Fix a coordinate $i$. For $F$ on the cube let
--   $$
--   m_iF(x)=\frac{F(x^{i\to0})+F(x^{i\to1})}{2},\qquad d_iF(x)=\frac{F(x^{i\to1})-F(x^{i\to0})}{2}.
--   $$
--   Let $T^{(i)}_u$ be the noise operator acting only on the coordinates other than $i$, normalized by averaging over the coordinate $i$ of the summation variable. Then for every $x$ and bit $b$,
--   $$
--   (T_uF)\bigl(x^{i\to b}\bigr)=\bigl(T^{(i)}_um_iF\bigr)(x)+\begin{cases}u,&b=1\\-u,&b=0\end{cases}\cdot\bigl(T^{(i)}_ud_iF\bigr)(x).
--   $$
--
--   Along the coordinate $i$, the noise multiplies the half-difference by $\pm u$ and leaves the pair mean alone. This is what makes coordinate sorting compatible with the noise operator.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Rearrangement.lean#L220-L238

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.noiseOperator_setBit (i : Fin n) (u : ℝ) (F : Cube n → ℝ)
    (x : Cube n) (b : Bool) :
    noiseOperator u F (setBit i b x) =
      coordinateOffNoise i u (coordinatePairMean i F) x +
        (if b then u else -u) * coordinateOffNoise i u (coordinatePairDifference i F) x := by sorry
