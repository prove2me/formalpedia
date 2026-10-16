-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_kernel_convolution
-- name    : OAI.Thorp.Fourier.Family.kernel_convolution
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:39:39.388974+00:00
-- url     : https://prove2.me/theorems/f73d2ecb-9cba-40c2-a72b-45b245f9f3b4
-- title:
--   Character kernels of a complete family of irreducibles are orthogonal idempotents under convolution
-- statement:
--   Let $G$ be a finite group and let $(\rho_i,V_i)_{i\in\Lambda}$ be a *complete family of irreducible unitary representations* of $G$: $\Lambda$ is a finite index set and, for each $i\in\Lambda$, $V_i$ is a finite-dimensional complex inner product space of dimension $d_i\ge 1$ on which $G$ acts irreducibly by unitary operators $\rho_i(g)$; distinct indices give non-isomorphic representations; and the characters $\chi_i(g)=\operatorname{tr}\rho_i(g)$ satisfy the regular-representation identity $\sum_{i\in\Lambda}d_i\,\chi_i(g)=|G|\,[g=1]$ for all $g\in G$.
--
--   For $i\in\Lambda$ let $e_i\colon G\to\mathbb C$ be the character kernel $e_i(g)=\frac{d_i}{|G|}\,\chi_i(g^{-1})$, and for functions $f,k\colon G\to\mathbb C$ let $(f*k)(x)=\sum_{g\in G}f(g)\,k(g^{-1}x)$ be their convolution. Then for all $i,j\in\Lambda$
--
--   $$
--   e_i*e_j=\begin{cases}e_i, & i=j,\\ 0, & i\neq j.\end{cases}
--   $$
--
--   Thus the character kernels are pairwise orthogonal idempotents of the group algebra $(\mathbb C^G,*)$. Since $f\mapsto\sigma(f)=\sum_g f(g)\,\sigma(g)$ turns convolution into composition for every representation $\sigma$ of $G$, this identity is what makes the operators $\sigma(e_i)$ mutually annihilating idempotents (the isotypic projectors), and its coordinatewise version gives the same property for the joint projectors of a product group $G^I$.
--
--   **Formalization Note** The family is a term `F : OAI.Thorp.Fourier.Family G`; $d_i$ is `F.degree i`, $e_i$ is `F.kernel i`, and the convolution is `OAI.Thorp.Fourier.convolution`. The right-hand side is written `if i = j then F.kernel i else 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean#L100-L113

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
variable {G : Type} [Group G] [Fintype G] (F : Family G)

theorem OAI.Thorp.Fourier.Family.kernel_convolution (i j : F.Index) : convolution (F.kernel i) (F.kernel j) =
    if i = j then F.kernel i else 0 := by sorry
