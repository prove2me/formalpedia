-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_joint_degree_le
-- name    : OAI.Thorp.Fourier.Family.joint_degree_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:46:50.619124+00:00
-- url     : https://prove2.me/theorems/1ef421fe-3cb3-4e01-be4b-012b97297dd4
-- title:
--   A nonzero joint isotypic projector of $H^I$ forces $\prod_i d_{a_i}\le\dim E$
-- statement:
--   Let $H$ be a finite group and let $(\rho_b,V_b)_{b\in\Lambda}$ be a complete family of irreducible unitary representations of $H$: $\Lambda$ is a finite index set and, for each $b\in\Lambda$, $V_b$ is a finite-dimensional complex inner product space of dimension $d_b\ge 1$ on which $H$ acts irreducibly by unitary operators $\rho_b(h)$; distinct indices give non-isomorphic representations; and the characters $\chi_b(h)=\operatorname{tr}\rho_b(h)$ satisfy the regular-representation identity $\sum_{b\in\Lambda}d_b\,\chi_b(h)=|H|\,[h=1]$ for all $h\in H$. Let $e_b(h)=\frac{d_b}{|H|}\,\chi_b(h^{-1})$ be the character kernels.
--
--   Let $I$ be a finite set and let $H^I$ be the product group of all maps $g\colon I\to H$ with pointwise multiplication. For a multi-index $a\colon I\to\Lambda$ define the joint kernel $K_a(g)=\prod_{i\in I}e_{a_i}(g_i)$. Let $E$ be a finite-dimensional complex vector space, let $\rho$ be a representation of $H^I$ on $E$, and let $P_a=\sum_{g\in H^I}K_a(g)\,\rho(g)$ be the joint isotypic projector of $a$. If $P_a\neq0$, then
--
--   $$
--   \prod_{i\in I}d_{a_i}\le\dim_{\mathbb C}E .
--   $$
--
--   In representation-theoretic terms, $P_a$ projects onto the part of $E$ on which $H^I$ acts through copies of the tensor product $\bigotimes_{i\in I}V_{a_i}$, a representation of dimension $\prod_i d_{a_i}$; the theorem says that this part can be nonzero only if that dimension fits into $E$. It is used to show that, for every multi-index occurring in $E$, the smallest degree $d$ among its factors satisfies $d^{|I|}\le\dim E$.
--
--   **Formalization Note** No inner product or unitarity is assumed on $E$ or $\rho$. The joint projector is `F.jointProjector ρ a`, built from the joint kernel `F.jointKernel a`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/JointProjectors.lean#L153-L171

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
variable {H : Type} [Group H] [Fintype H] (F : Family H)
variable {I : Type} [Fintype I]
variable {E : Type uE} [AddCommGroup E] [Module ℂ E]

theorem OAI.Thorp.Fourier.Family.joint_degree_le [FiniteDimensional ℂ E] (ρ : Representation ℂ (I → H) E)
    (a : I → F.Index) (ha : F.jointProjector ρ a ≠ 0) :
    (∏ i, F.degree (a i)) ≤ Module.finrank ℂ E := by sorry
