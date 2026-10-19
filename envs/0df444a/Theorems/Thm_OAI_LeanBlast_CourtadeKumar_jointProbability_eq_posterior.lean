-- Prove2me | Theorems.Thm_OAI_LeanBlast_CourtadeKumar_jointProbability_eq_posterior
-- name    : OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T10:54:07.510799+00:00
-- url     : https://prove2.me/theorems/2970a3d0-c833-49d4-937a-bcfdcdfc486a
-- title:
--   The joint law of $f(X)$ and a noisy copy of $X$ through the noise operator
-- statement:
--   Let $X$ be uniform on $\{0,1\}^n$ and $Y$ obtained from $X$ by flipping each bit independently with probability $\varepsilon$. For $f:\{0,1\}^n\to\{0,1\}$, let $p(b,y)=\Pr[f(X)=b,\ Y=y]$, i.e. $2^{-n}\sum_{x:f(x)=b}\prod_i\bigl(1-\varepsilon$ or $\varepsilon\bigr)$, according as $x_i=y_i$ or not. Let $f^\pm=\pm1$ be the sign encoding of $f$ and $T_u$ the noise operator. Then for every $b$ and $y$,
--   $$
--   p(b,y)=2^{-n}\cdot\begin{cases}\dfrac{1+(T_{1-2\varepsilon}f^\pm)(y)}{2},&b=\mathrm{true},\\\dfrac{1-(T_{1-2\varepsilon}f^\pm)(y)}{2},&b=\mathrm{false}.\end{cases}
--   $$
--
--   Given the noisy observation $y$, the conditional law of $f(X)$ is that of a sign with mean $(T_{1-2\varepsilon}f^\pm)(y)$. So the mutual information is an entropy deficit of the noise-smoothed function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/BooleanNoise/FiniteDistribution.lean#L70-L85

import Mathlib
import Definitions.Def_CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Model__CourtadeKumar
import Definitions.Def_OAI_Combinatorics_GotsmanLinial_Statement__CourtadeKumar
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Basic
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteNoise
import Definitions.Def_OAI_InformationTheory_BooleanNoise_Statement
import Definitions.Def_OAI_InformationTheory_BooleanNoise_EntropyScalars
import Definitions.Def_OAI_InformationTheory_BooleanNoise_FiniteDistribution

open OAI OAI.LeanBlast OAI.LeanBlast.CourtadeKumar
open scoped BigOperators
variable {n : ℕ}

theorem OAI.LeanBlast.CourtadeKumar.jointProbability_eq_posterior (ε : ℝ) (f : Cube n → Bool) (b : Bool) (y : Cube n) :
    jointProbability ε f b y =
      signProbability (noiseOperator (1 - 2 * ε) (signEncoding f) y) b / (2 : ℝ) ^ n := by sorry
