-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_entropy_normalization_error
-- name    : OAI.ThorpCompatibility.entropy_normalization_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:06:44.227874+00:00
-- url     : https://prove2.me/theorems/7c4cc95e-c941-43e8-96a9-edc395f4aa14
-- title:
--   The total exposure error at threshold $m^{1/100}$, plus $2+2\log m$, is at most $50000\,m^{1.08}$
-- statement:
--   For natural numbers $A,D$ and reals $H,K$ let
--   $$
--   E_{A,D}(H,K)=A(1+\log D)+2DKH(1+\log D)\,\mathcal H_A
--   $$
--   be the total exposure error, where $\mathcal H_A=\sum_{t=1}^{A}\frac1t$ is the $A$-th harmonic number. Let $m\ge1$ be real and let $A,D\ge1$ be natural numbers with $A\le2m$ and $D\le2m$. Then
--   $$
--   E_{A,D}\big(m^{1/100},m^{1/100}\big)+2+2\log m\le50000\,m^{108/100}.
--   $$
--
--   This collects the lower-order errors of the weighted compatibility bound. When $AD=m^2$, the logarithm of the normalizing factor $(AD)!/((D!)^A(A!)^D)$ exceeds $AD$ by at most $1+\log(AD)=1+2\log m$, and the entropy estimate contributes the exposure error and a further additive $1$. The theorem bounds the total by $50000\,m^{1.08}=50000\,(AD)^{0.54}$, which produces the factor $\exp(C_0\,n^{54/100})$ with $C_0=50000$.
--
--   **Formalization Note** $\mathcal H_A$ is Mathlib's `harmonic A` cast to $\mathbb{R}$, $E_{A,D}$ is `totalExposureError`, and $m^{1/100}$ and $m^{108/100}$ are real powers (`Real.rpow`). The constant $50000$ is not optimized.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/Normalization.lean#L56-L84

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments
import Definitions.Def_OAI_Probability_ThorpCompatibility_HeavyEntries
import Definitions.Def_OAI_Probability_ThorpCompatibility_ExposureEntropy

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset

theorem OAI.ThorpCompatibility.entropy_normalization_error {m : ℝ} (hm : 1 ≤ m) {A D : ℕ}
    (hA0 : 0 < A) (hD0 : 0 < D) (hA : (A:ℝ) ≤ 2*m) (hD : (D:ℝ) ≤ 2*m) :
    totalExposureError A D (m^(1/100:ℝ)) (m^(1/100:ℝ)) + 2 + 2*Real.log m ≤
      50000*m^(108/100:ℝ) := by sorry
