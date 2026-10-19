-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_informationDeficit_noise_dictator
-- name    : OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:55:42.842163+00:00
-- url     : https://prove2.me/theorems/7b22b120-ed20-4be5-8b2e-2ff654fce810
-- title:
--   The information deficit of a noisy dictator equals $\psi(u)$
-- statement:
--   On the Boolean cube $\{0,1\}^n$, $\mathbb{E}g=2^{-n}\sum_xg(x)$ is the uniform average, and the noise operator with correlation $u$ is $(T_ug)(x)=\sum_yK_u(x,y)g(y)$ with $K_u(x,y)=\prod_i\frac{1\pm u}{2}$ ($+$ where $x_i=y_i$, $-$ otherwise). Let $\psi(v)=\frac{1+v}{2}\log(1+v)+\frac{1-v}{2}\log(1-v)$ and $h(v)=\log2-\psi(v)$. The information deficit of $g$ is $h(\mathbb{E}g)-\mathbb{E}\,h(g)$. Let $\chi_i=\pm1$ be the sign encoding of the dictator $x\mapsto x_i$. Then for every $u$,
--   $$
--   h\bigl(\mathbb{E}\,T_u\chi_i\bigr)-\mathbb{E}\,h\bigl(T_u\chi_i\bigr)=\psi(u).
--   $$
--
--   In bits, this is the statement that a dictator observed through a binary symmetric channel with $u=1-2\varepsilon$ carries exactly $1-H(\varepsilon)$ bits of information about its input. That is the attainment half of the Courtade–Kumar statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/Attainment.lean#L106-L119

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

theorem OAI.LeanBlast.CourtadeKumar.informationDeficit_noise_dictator (u : ℝ) (i : Fin n) :
    informationDeficit (noiseOperator u (signEncoding (dictator i))) = psi u := by sorry
