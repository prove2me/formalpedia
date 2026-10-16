-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_sum_sq
-- name    : OAI.Thorp.Fourier.Family.kernel_sum_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:44:23.124564+00:00
-- url     : https://prove2.me/theorems/0c71b134-6b6b-4273-827a-f333ef76e0f4
-- title:
--   Plancherel identity for a partial sum of character kernels
-- statement:
--   Let $G$ be a finite group and let $(\rho_i,V_i)_{i\in\Lambda}$ be a complete family of irreducible unitary representations of $G$: $\Lambda$ is a finite index set and, for each $i\in\Lambda$, $V_i$ is a finite-dimensional complex inner product space of dimension $d_i\ge 1$ on which $G$ acts irreducibly by unitary operators $\rho_i(g)$; distinct indices give non-isomorphic representations; and the characters $\chi_i(g)=\operatorname{tr}\rho_i(g)$ satisfy the regular-representation identity $\sum_{i\in\Lambda}d_i\,\chi_i(g)=|G|\,[g=1]$ for all $g\in G$. For $i\in\Lambda$ let $e_i(g)=\frac{d_i}{|G|}\,\chi_i(g^{-1})$ be its character kernel.
--
--   Then for every finite set $s\subseteq\Lambda$ of indices,
--
--   $$
--   |G|\sum_{g\in G}\Big|\sum_{i\in s}e_i(g)\Big|^2=\sum_{i\in s}d_i^2 .
--   $$
--
--   This is the Plancherel identity for the function $\sum_{i\in s}e_i$, which is the kernel of the projector onto the isotypic components indexed by $s$. It computes the exact $\ell^2$-mass of that kernel, the constant that appears when the Cauchy–Schwarz inequality is used to bound matrix coefficients of vectors lying in those isotypic components.
--
--   **Formalization Note** The absolute value is the complex modulus; $d_i$ is `F.degree i` and $e_i$ is `F.kernel i` for `F : OAI.Thorp.Fourier.Family G`, and the identity is stated in the real numbers.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean#L182-L220

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

open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
universe uG uE uV
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable {G : Type} [Group G] [Fintype G] (F : Family G)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem OAI.Thorp.Fourier.Family.kernel_sum_sq (s : Finset F.Index) :
    (Fintype.card G : ℝ) * ∑ g, ‖∑ i ∈ s, F.kernel i g‖ ^ 2 = ∑ i ∈ s, (F.degree i : ℝ) ^ 2 := by sorry
