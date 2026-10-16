-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_integrated_kernel
-- name    : OAI.Thorp.Fourier.Family.integrated_kernel
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:38:40.725091+00:00
-- url     : https://prove2.me/theorems/df6b806c-c3e3-4759-aa75-74efb59ec046
-- title:
--   Character kernels of a Fourier family act on its members as $\delta_{ij}$ times the identity
-- statement:
--   Let $G$ be a finite group with a Fourier family $(\rho_i)_{i\in\widehat{G}}$: a finite index set $\widehat{G}$ and, for each $i$, a finite-dimensional complex inner product space $V_i$ of dimension $d_i>0$ with an irreducible unitary representation $\rho_i$ of $G$, such that $\rho_i\cong\rho_j$ only if $i=j$, and such that $\sum_i d_i\chi_i(g)$ equals $|G|$ for $g=1$ and $0$ otherwise, where $\chi_i(g)=\operatorname{tr}\rho_i(g)$. Let
--   $$k_i(g)=\frac{d_i}{|G|}\,\chi_i(g^{-1})$$
--   be the character kernel of $\rho_i$. Then for all $i,j\in\widehat{G}$,
--
--   $$
--   \sum_{g\in G}k_i(g)\,\rho_j(g)=\begin{cases}\mathrm{id}_{V_j}, & i=j,\\ 0, & i\ne j.\end{cases}
--   $$
--
--   In other words, the isotypic projector $P_i=\sum_g k_i(g)\rho(g)$ acts as the identity on the member $\rho_i$ of the family and kills every other member. This is the basic computation behind the Fourier decomposition on $G$: from it one derives that the $P_i$ are idempotent, mutually annihilating and sum to the identity in every representation, i.e. that they are the projections onto the isotypic components.
--
--   **Formalization Note** The left-hand side is `integrated (F.rep j) (F.kernel i)`, with `integrated ρ f = ∑ g, f g • ρ g`; the right-hand side is `if i = j then 1 else 0` in `Module.End ℂ (F.Space j)`. The family is a structure `F : Family G` whose fields encode the hypotheses listed above.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FourierFamilies.lean#L78-L98

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

theorem OAI.Thorp.Fourier.Family.integrated_kernel (i j : F.Index) : integrated (F.rep j) (F.kernel i) = if i = j then 1 else 0 := by sorry
