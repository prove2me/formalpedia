-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_splitVector_low
-- name    : OAI.Thorp.Fourier.Family.splitVector_low
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:47:35.94914+00:00
-- url     : https://prove2.me/theorems/d74504c5-71bb-4260-9d31-c1832654c13f
-- title:
--   Least-factor pieces lie in the low-degree isotypic part of their coordinate
-- statement:
--   Let $H$ be a finite group and let $(\rho_b,V_b)_{b\in\Lambda}$ be a complete family of irreducible unitary representations of $H$: $\Lambda$ is a finite index set and, for each $b\in\Lambda$, $V_b$ is a finite-dimensional complex inner product space of dimension $d_b\ge 1$ on which $H$ acts irreducibly by unitary operators $\rho_b(h)$; distinct indices give non-isomorphic representations; and the characters $\chi_b(h)=\operatorname{tr}\rho_b(h)$ satisfy the regular-representation identity $\sum_{b\in\Lambda}d_b\,\chi_b(h)=|H|\,[h=1]$ for all $h\in H$. Let $e_b(h)=\frac{d_b}{|H|}\,\chi_b(h^{-1})$ be the character kernels.
--
--   Let $I$ be a finite nonempty set with $n=|I|$ elements, let $H^I$ be the product group, and for $i\in I$ let $\iota_i\colon H\to H^I$ put $h$ in coordinate $i$ and $1$ elsewhere. Let $E$ be a finite-dimensional complex inner product space of dimension $D$ and $\rho$ a representation of $H^I$ on $E$. Define:
--
--   1. for a multi-index $a\colon I\to\Lambda$, the joint projector $P_a=\sum_{g\in H^I}\big(\prod_{j\in I}e_{a_j}(g_j)\big)\rho(g)$;
--   2. a least factor $\ell(a)\in I$, a fixed choice of coordinate with $d_{a_{\ell(a)}}\le d_{a_j}$ for all $j\in I$;
--   3. for $v\in E$ and $i\in I$, the $i$-th least-factor piece $z_i(v)=\sum_{a:\ \ell(a)=i}P_a v$;
--   4. for $b\in\Lambda$, the coordinate isotypic projector $P^{(i)}_b=\sum_{h\in H}e_b(h)\,\rho(\iota_i(h))$.
--
--   Then for every $v\in E$ and $i\in I$,
--
--   $$
--   \sum_{b\in\Lambda:\ d_b^{\,n}\le D}P^{(i)}_b\,z_i(v)=z_i(v).
--   $$
--
--   In other words, in the $i$-th coordinate the piece $z_i(v)$ only involves irreducible representations of $H$ of degree at most $D^{1/n}$. The pieces $z_i(v)$ sort the joint isotypic components of $v$ according to which coordinate carries the smallest degree, and this statement allows one to apply, separately to each piece, a matrix-coefficient bound whose constant is the small sum $\sum_{d_b^n\le D}d_b^2$.
--
--   **Formalization Note** The least factor is `F.leastFactor a`, defined by a choice (`Classical.choose`) of a minimizing coordinate, and $z_i(v)$ is `F.splitVector ρ v i`. The representation $\rho$ need not be unitary, and the inner product on $E$ plays no role in this statement. The coordinate representation is `ρ.comp (MonoidHom.mulSingle _ i)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/ProductProjectors.lean#L170-L186

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

open OAI OAI.Thorp OAI.Thorp.Fourier OAI.Thorp.Fourier.Family
universe uH uI uE uJ
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical
variable {H I : Type} [Group H] [Fintype H] [Fintype I] [Nonempty I] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem OAI.Thorp.Fourier.Family.splitVector_low (ρ : Representation ℂ (I → H) E) (v : E) (i : I) :
    (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
      F.projector (ρ.comp (MonoidHom.mulSingle (fun _ : I => H) i)) b) (F.splitVector ρ v i) =
        F.splitVector ρ v i := by sorry
