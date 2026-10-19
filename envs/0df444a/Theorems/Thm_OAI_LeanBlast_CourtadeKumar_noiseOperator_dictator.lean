-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_noiseOperator_dictator
-- name    : OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:54:42.888795+00:00
-- url     : https://prove2.me/theorems/b9fb64f5-6110-4252-b9ca-b2d9f65d7e78
-- title:
--   Dictators are eigenfunctions of the noise operator with eigenvalue $u$
-- statement:
--   On the Boolean cube $\{0,1\}^n$, $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and the noise operator with correlation $u$ is $(T_ug)(x)=\sum_yK_u(x,y)g(y)$ with $K_u(x,y)=\prod_i\frac{1\pm u}{2}$ ($+$ where $x_i=y_i$, $-$ otherwise). For a coordinate $i$, let $\chi_i(x)=1$ if $x_i$ is true and $-1$ otherwise, the sign encoding of the dictator $x\mapsto x_i$. Then for every $u$ and $x$,
--   $$
--   (T_u\chi_i)(x)=u\,\chi_i(x).
--   $$
--
--   Noise multiplies a degree-one character by its correlation. This is the computation behind the fact that dictators attain the Courtade–Kumar bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Attainment.lean#L16-L37

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

theorem OAI.LeanBlast.CourtadeKumar.noiseOperator_dictator (u : ℝ) (i : Fin n) (x : Cube n) :
    noiseOperator u (signEncoding (dictator i)) x =
      u * signEncoding (dictator i) x := by sorry
