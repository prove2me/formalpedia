-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_Family_integrated_norm_sq
-- name    : OAI.Thorp.Fourier.Family.integrated_norm_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:48:28.503439+00:00
-- url     : https://prove2.me/theorems/e66abc67-ff69-42c0-8e31-379214111b72
-- title:
--   Coset caps on coordinate subgroups bound the averaging operator of an irreducible unitary representation
-- statement:
--   Let $G$ and $H$ be finite groups, $I$ a finite nonempty set, and $(\rho_b,V_b)_{b\in\Lambda}$ a complete family of irreducible unitary representations of $H$: $\Lambda$ is a finite index set and, for each $b\in\Lambda$, $V_b$ is a finite-dimensional complex inner product space of dimension $d_b\ge 1$ on which $H$ acts irreducibly by unitary operators $\rho_b(h)$; distinct indices give non-isomorphic representations; and the characters $\chi_b(h)=\operatorname{tr}\rho_b(h)$ satisfy the regular-representation identity $\sum_{b\in\Lambda}d_b\,\chi_b(h)=|H|\,[h=1]$ for all $h\in H$. For $i\in I$ let $\iota_i\colon H\to H^I$ put $h$ in coordinate $i$ and $1$ elsewhere.
--
--   Let $E$ be a finite-dimensional complex inner product space of dimension $D\neq0$, and let $\rho$ be an irreducible representation of $G$ on $E$ which is unitary: $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$. Let $\psi\colon H^I\to G$ be a group homomorphism, let $\nu\colon G\to\mathbb R$ be a probability vector ($\nu(g)\ge0$ and $\sum_g\nu(g)=1$), and let $B\ge0$ be such that for all $i\in I$ and $g\in G$
--   $$
--   \sum_{h\in H}\nu\big(g\,\psi(\iota_i(h))\big)\le\frac{B\,|H|}{|G|}.
--   $$
--   Write $\rho(\nu)=\sum_{g\in G}\nu(g)\,\rho(g)$. Then for every $v\in E$
--
--   $$
--   \|\rho(\nu)v\|^2\le\frac{|I|\,B}{D}\Big(\sum_{b\in\Lambda:\ d_b^{|I|}\le D}d_b^2\Big)\|v\|^2 .
--   $$
--
--   The hypothesis says that $\nu$ gives every left coset of each coordinate subgroup $\psi(\iota_i(H))$ at most $B$ times the mass of the uniform distribution. The conclusion bounds the operator norm of the averaging operator $\rho(\nu)$ in terms of the dimension of $\rho$ and the low-degree part of the Plancherel mass $\sum_b d_b^2$ of $H$; it is the general mechanism that turns coset caps into decay in every irreducible unitary representation.
--
--   **Formalization Note** The averaging operator is `integrated ρ (fun g => (ν g : ℂ))`. The homomorphism $\psi$ need not be injective; the coset sum runs over $h\in H$, with multiplicity. The hypothesis $D\neq0$ is stated explicitly.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/CosetBounds.lean#L154-L185

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
universe uG uH uE uJ
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped Classical
variable {G H I : Type} [Group G] [Fintype G] [Group H] [Fintype H]
  [Fintype I] [Nonempty I] (F : Family H)
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

theorem OAI.Thorp.Fourier.Family.integrated_norm_sq (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (ψ : (I → H) →* G) (ν : G → ℝ) (B : ℝ)
    (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1) (hB : 0 ≤ B)
    (hcoset : ∀ i g, ∑ h, ν (g * ψ (Pi.mulSingle i h)) ≤
      B * (Fintype.card H : ℝ) / Fintype.card G) (v : E) :
    ‖integrated ρ (fun g => (ν g : ℂ)) v‖ ^ 2 ≤
      (Fintype.card I : ℝ) * B *
        (∑ b ∈ Finset.univ.filter (fun b => F.degree b ^ Fintype.card I ≤ Module.finrank ℂ E),
          (F.degree b : ℝ)^2) / Module.finrank ℂ E * ‖v‖ ^ 2 := by sorry
