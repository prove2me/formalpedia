-- Prove2me | Theorems.Thm_OAI_Thorp_Current_low_degree_first
-- name    : OAI.Thorp.Current.low_degree_first
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:53:42.992659+00:00
-- url     : https://prove2.me/theorems/b7e51b20-aa0a-46a4-b596-916378590891
-- title:
--   Low-degree Plancherel mass is at most $D^{3/8}$ times the inverse-degree sum
-- statement:
--   Let $H$ be a finite group and let $(\rho_b,V_b)_{b\in\Lambda}$ be a complete family of irreducible unitary representations of $H$: $\Lambda$ is a finite index set and, for each $b\in\Lambda$, $V_b$ is a finite-dimensional complex inner product space of dimension $d_b\ge 1$ on which $H$ acts irreducibly by unitary operators $\rho_b(h)$; distinct indices give non-isomorphic representations; and the characters $\chi_b(h)=\operatorname{tr}\rho_b(h)$ satisfy the regular-representation identity $\sum_{b\in\Lambda}d_b\,\chi_b(h)=|H|\,[h=1]$ for all $h\in H$. Then for every natural number $D$,
--
--   $$
--   \sum_{b\in\Lambda:\ d_b^{8}\le D}d_b^{2}\ \le\ D^{3/8}\sum_{b\in\Lambda}\frac1{d_b}.
--   $$
--
--   The summation condition $d_b^8\le D$ means $d_b\le D^{1/8}$, the low-degree range that arises for products of eight copies of $H$. The inequality converts the low-degree part of the Plancherel mass $\sum_b d_b^2$ into the first inverse-degree moment $\sum_b 1/d_b$; whenever the latter is uniformly bounded, as for the symmetric groups, this yields a bound of order $D^{3/8}$.
--
--   **Formalization Note** $D^{3/8}$ is the real power `Real.rpow` with $D$ cast to a real number. The proof only uses that every degree is positive.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FirstFourier.lean#L15-L41

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
import Definitions.Def_OAI_Probability_ThorpShuffle_ProductProjectors
import Definitions.Def_OAI_Probability_ThorpShuffle_SymmetricFamilies
import Definitions.Def_OAI_Probability_ThorpShuffle_BlockEmbedding

open OAI OAI.Thorp OAI.Thorp.Current
universe uE
open scoped BigOperators Classical ComplexConjugate InnerProductSpace
open Thorp.Fourier

theorem OAI.Thorp.Current.low_degree_first {H : Type} [Group H] [Fintype H]
    (F : Fourier.Family H) (D : ℕ) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ 8 ≤ D), (F.degree b : ℝ)^2) ≤
      (D : ℝ) ^ (3 / 8 : ℝ) * ∑ b, (F.degree b : ℝ)⁻¹ := by sorry
