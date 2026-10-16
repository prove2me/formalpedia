-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_coefficient_evaluation
-- name    : OAI.Thorp.Fourier.Family.coefficient_evaluation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:45:20.907987+00:00
-- url     : https://prove2.me/theorems/917cfcaf-be19-48ba-995c-9a3168c2c108
-- title:
--   Cauchy–Schwarz bound for a coefficient of a vector supported on few isotypic components
-- statement:
--   Let $G$ be a finite group and let $(\rho_i,V_i)_{i\in\Lambda}$ be a complete family of irreducible unitary representations of $G$: $\Lambda$ is a finite index set and, for each $i\in\Lambda$, $V_i$ is a finite-dimensional complex inner product space of dimension $d_i\ge 1$ on which $G$ acts irreducibly by unitary operators $\rho_i(g)$; distinct indices give non-isomorphic representations; and the characters $\chi_i(g)=\operatorname{tr}\rho_i(g)$ satisfy the regular-representation identity $\sum_{i\in\Lambda}d_i\,\chi_i(g)=|G|\,[g=1]$ for all $g\in G$. Let $e_i(g)=\frac{d_i}{|G|}\,\chi_i(g^{-1})$ be the character kernels.
--
--   Let $E$ be a complex inner product space, with inner product $\langle\cdot,\cdot\rangle$ conjugate-linear in the first argument, and let $\rho$ be any representation of $G$ on $E$ by linear maps. For $i\in\Lambda$ let $P_i=\sum_{g\in G}e_i(g)\,\rho(g)$ be the corresponding isotypic projector. Let $s\subseteq\Lambda$ be a finite set and let $v,w\in E$ satisfy $\sum_{i\in s}P_i\,v=v$. Then
--
--   $$
--   |G|\,\big|\langle w,v\rangle\big|^2\le\Big(\sum_{i\in s}d_i^2\Big)\sum_{g\in G}\big|\langle w,\rho(g)v\rangle\big|^2 .
--   $$
--
--   So if $v$ lies in the isotypic components indexed by $s$, a single coefficient $\langle w,v\rangle$ is controlled by the average of the coefficients along the orbit of $v$, at the price of the factor $\sum_{i\in s}d_i^2$. Applied to the restriction of a representation to a subgroup, it compares one matrix coefficient with its sum over a coset, which is how small degrees are converted into norm bounds for averaging operators.
--
--   **Formalization Note** Neither unitarity of $\rho$ nor finite-dimensionality of $E$ is assumed. $P_i$ is `F.projector ρ i` and $d_i$ is `F.degree i`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/JointProjectors.lean#L26-L40

import Mathlib
import Definitions.Def_ThorpFirstReciprocal
import Definitions.Def_OAI_Probability_ThorpShuffle_Model
import Definitions.Def_OAI_Probability_ThorpShuffle_PairAveraging
import Definitions.Def_OAI_Probability_ThorpShuffle_Walsh
import Definitions.Def_OAI_Probability_ThorpShuffle_Support
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FiniteExpectation
import Definitions.Def_OAI_Probability_ThorpShuffle_WalshFlow
import Definitions.Def_OAI_Probability_ThorpShuffle_FreshCoins
import Definitions.Def_OAI_Probability_ThorpShuffle_HalfHistories
import Definitions.Def_OAI_Probability_ThorpShuffle_NoiseEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_EnergyDecay
import Definitions.Def_OAI_Probability_ThorpShuffle_MarginalEnergy
import Definitions.Def_OAI_Probability_ThorpShuffle_ConditionalLaw
import Definitions.Def_OAI_Probability_ThorpShuffle_TaggedCompletion
import Definitions.Def_OAI_Probability_ThorpShuffle_Reachability
import Definitions.Def_OAI_Probability_ThorpShuffle_Cyclic
import Definitions.Def_OAI_Probability_ThorpShuffle_Tableaux
import Definitions.Def_OAI_Probability_ThorpShuffle_Specht
import Definitions.Def_OAI_Probability_ThorpShuffle_Polytabloids
import Definitions.Def_OAI_Probability_ThorpShuffle_Irreducibility
import Definitions.Def_OAI_Probability_ThorpShuffle_Classification
import Definitions.Def_OAI_Probability_ThorpShuffle_LinearExtensions
import Definitions.Def_OAI_Probability_ThorpShuffle_ExtensionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_PartitionBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_DegreeBounds
import Definitions.Def_OAI_Probability_ThorpShuffle_FirstMoment
import Definitions.Def_OAI_Probability_ThorpShuffle_Reynolds
import Definitions.Def_OAI_Probability_ThorpShuffle_FourierFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_JointProjectors

open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
universe uI uE
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem OAI.Thorp.Fourier.Family.coefficient_evaluation (ρ : Representation ℂ G E) (s : Finset F.Index)
    (v w : E) (hv : (∑ i ∈ s, F.projector ρ i) v = v) :
    (Fintype.card G : ℝ) * ‖⟪w, v⟫_ℂ‖ ^ 2 ≤
      (∑ i ∈ s, (F.degree i : ℝ)^2) * ∑ g, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 := by sorry
