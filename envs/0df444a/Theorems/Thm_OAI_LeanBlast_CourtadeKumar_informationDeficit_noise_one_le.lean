-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_informationDeficit_noise_one_le
-- name    : OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:55:12.483563+00:00
-- url     : https://prove2.me/theorems/41858d2d-e8f4-45e2-b3f4-9cbaf8fa34e2
-- title:
--   Without noise, the information deficit of a sign function is at most $\log 2$
-- statement:
--   On the Boolean cube $\{0,1\}^n$, $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and the noise operator with correlation $u$ is $(T_ug)(x)=\sum_yK_u(x,y)g(y)$ with $K_u(x,y)=\prod_i\frac{1\pm u}{2}$ ($+$ where $x_i=y_i$, $-$ otherwise). Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$. The information deficit of $g$ is $h(\mathbb{E}g)-\mathbb{E}\,h(g)$.
--
--   If $g$ is sign-valued ($g(x)\in\{\pm1\}$ for all $x$), then
--   $$
--   h\bigl(\mathbb{E}\,T_1g\bigr)-\mathbb{E}\,h\bigl(T_1g\bigr)\le\psi(1)=\log2 .
--   $$
--
--   At correlation $1$ there is no noise, and the mutual information of a Boolean function with its input is its entropy, at most one bit. This is the endpoint $u=1$ of the Courtade–Kumar bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Attainment.lean#L92-L104

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

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_one_le (g : Cube n → ℝ) (hg : IsSignValued g) :
    informationDeficit (noiseOperator 1 g) ≤ psi 1 := by sorry
