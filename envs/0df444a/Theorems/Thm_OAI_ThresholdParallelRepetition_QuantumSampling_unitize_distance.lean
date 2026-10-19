-- Prove2me | Theorems.Thm_OAI_ThresholdParallelRepetition_QuantumSampling_unitize_distance
-- name    : OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T11:14:43.880215+00:00
-- url     : https://prove2.me/theorems/20774776-756a-46ac-938b-fadf5c7cb693
-- title:
--   Distance from a matrix to its Frobenius normalization
-- statement:
--   Let $m$, $n$ be finite index sets and, for $M\in\mathbb{C}^{m\times n}$, let $\|M\|_F=\bigl(\sum_{a,b}|M_{ab}|^2\bigr)^{1/2}$ be its Frobenius (Hilbert–Schmidt) norm. For $C,D\in\mathbb{C}^{m\times n}$ define the *normalization of $C$ with default $D$* by
--   $$\operatorname{unit}(C,D)=\begin{cases}C/\|C\|_F,&C\neq0,\\ D,&C=0.\end{cases}$$
--   If $\|D\|_F=1$, then
--
--   $$
--   \bigl\|C-\operatorname{unit}(C,D)\bigr\|_F^2=\bigl(\|C\|_F-1\bigr)^2 .
--   $$
--
--   When $D$ has unit norm, $\operatorname{unit}(C,D)$ always has unit norm, and the identity says that the squared cost of rescaling $C$ to a unit vector is exactly the squared deviation of its norm from $1$; the default $D$ is used only for $C=0$, where both sides equal $1$. Viewing $C$ as a possibly subnormalized bipartite vector, this converts information about norms into a bound on the distance to a genuine unit state. When $\|C\|_F^2=a$ is a density value, the right-hand side is the Hellinger-type term $(\sqrt a-1)^2$, which is how the identity is used to control normalization costs by relative entropy.
--
--   **Formalization Note** `unitize C D` is defined as `if hsSq C = 0 then D else (Real.sqrt (hsSq C))⁻¹ • C`, where `hsSq C` is $\|C\|_F^2$, and the hypothesis is `hsSq D = 1`. Since $\|C\|_F^2=0$ exactly when $C=0$, this is the case distinction above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/EntangledGames/BlockStates.lean#L93-L106

import Mathlib
import Definitions.Def_EntangledGames
import Definitions.Def_OAI_Probability_EntangledGames_Basic
import Definitions.Def_OAI_Probability_EntangledGames_Resolvent
import Definitions.Def_OAI_Probability_EntangledGames_SpectralEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Purification
import Definitions.Def_OAI_Probability_EntangledGames_MeasurementTransport
import Definitions.Def_OAI_Probability_EntangledGames_HilbertSchmidt
import Definitions.Def_OAI_Probability_EntangledGames_SpectralBins
import Definitions.Def_OAI_Probability_EntangledGames_CoherentFilters
import Definitions.Def_OAI_Probability_EntangledGames_SamplingStrategy
import Definitions.Def_OAI_Probability_EntangledGames_CorrelatedSampling
import Definitions.Def_OAI_Probability_EntangledGames_FiniteProbability
import Definitions.Def_OAI_Probability_EntangledGames_RelativeEntropy
import Definitions.Def_OAI_Probability_EntangledGames_Resampling
import Definitions.Def_OAI_Probability_EntangledGames_EffectExposure
import Definitions.Def_OAI_Probability_EntangledGames_ExposureChain
import Definitions.Def_OAI_Probability_EntangledGames_BlockStates

open OAI OAI.ThresholdParallelRepetition OAI.ThresholdParallelRepetition.QuantumSampling
universe u_m u_n u_R u_A u_B u_Z
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix
open scoped Matrix.Norms.Frobenius
variable {m : Type u_m} {n : Type u_n} [Fintype m] [Fintype n]

theorem OAI.ThresholdParallelRepetition.QuantumSampling.unitize_distance (C D : Matrix m n ℂ) (hD : hsSq D = 1) :
    hsSq (C-unitize C D) = (Real.sqrt (hsSq C)-1)^2 := by sorry
