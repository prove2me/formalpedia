-- Prove2me | Theorems.Thm_OAI_Thorp_Current_eight_block_of_cap
-- name    : OAI.Thorp.Current.eight_block_of_cap
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:59:31.839648+00:00
-- url     : https://prove2.me/theorems/d1a185d1-45cd-4b4a-a554-78fdc8b9fdd9
-- title:
--   Operator-norm decay $\sqrt{32C_1}\,D^{-5/16}$ under coset caps on eight symmetric-group blocks
-- statement:
--   **The constant $C_1$.** For $n\ge0$ and a partition $\lambda$ of $n$, let $M^\lambda$ be the complex inner product space with orthonormal basis the $\lambda$-tabloids (ways of distributing $\{1,\dots,n\}$ into rows of sizes $\lambda_1,\lambda_2,\dots$), on which the symmetric group $\mathfrak S_n$ acts by permuting entries. Fix a bijection $T$ between $\{1,\dots,n\}$ and the cells of the Young diagram of $\lambda$, let $C_T$ be the group of permutations preserving every column of $T$, and let $e_T=\sum_{\pi\in C_T}\operatorname{sgn}(\pi)\,\pi\{T\}$ be the polytabloid, where $\{T\}$ is the tabloid of $T$. The Specht module $S^\lambda\subseteq M^\lambda$ is the span of $\{\pi e_T:\pi\in\mathfrak S_n\}$, and $f^\lambda=\dim_{\mathbb C}S^\lambda$. Put
--   $$
--   R_1(n)=\sum_{\lambda\vdash n}\frac1{f^\lambda},\qquad C_1=\sup_{n\ge1}R_1(n).
--   $$
--
--   **The theorem.** Let $G$ be a finite group, $s\ge1$ an integer, and $\psi\colon(\mathfrak S_s)^8\to G$ a group homomorphism, where $\mathfrak S_s$ is the symmetric group on $s$ letters; for $i\in\{0,\dots,7\}$ let $\iota_i\colon\mathfrak S_s\to(\mathfrak S_s)^8$ put $h$ in coordinate $i$ and the identity elsewhere. Let $E$ be a finite-dimensional complex inner product space of dimension $D$ and $\rho$ an irreducible representation of $G$ on $E$ by unitary operators. Let $\nu\colon G\to\mathbb R$ satisfy $\nu(g)\ge0$ for all $g$ and $\sum_g\nu(g)=1$, and assume the coset caps
--   $$
--   \sum_{h\in\mathfrak S_s}\nu\big(g\,\psi(\iota_i(h))\big)\le\frac{4\,s!}{|G|}\qquad\text{for all }i\in\{0,\dots,7\}\text{ and }g\in G.
--   $$
--   Then the averaging operator satisfies
--
--   $$
--   \Big\|\sum_{g\in G}\nu(g)\,\rho(g)\Big\|_{\mathrm{op}}\le\sqrt{32\,C_1}\;D^{-5/16}.
--   $$
--
--   So a probability measure that gives every left coset of each of the eight block subgroups at most four times its uniform share contracts in every irreducible unitary representation, at a rate polynomial in the dimension. This is the form in which the bound is applied to permutations of the $2^d$ positions $\{0,1\}^d$ split into eight blocks of size $2^{d-3}$.
--
--   **Formalization Note** $C_1$ is `OAI.Thorp.Current.C1`, defined as `sSup` of the range of $R_1$ on $n\ge1$; boundedness of that range is proved along the way, so $C_1$ is the genuine supremum. $f^\lambda$ is the dimension of the concrete Specht module `Specht.Space p`, whose tableau is a fixed bijection chosen by `Fintype.equivOfCardEq`. $D^{-5/16}$ is a real power, and $D\ge1$ because irreducible representations are nonzero. The operator norm is that of `LinearMap.toContinuousLinearMap (integrated ρ (fun g => (ν g : ℂ)))`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/FirstFourier.lean#L43-L93

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

theorem OAI.Thorp.Current.eight_block_of_cap {G : Type} [Group G] [Fintype G]
    (s : ℕ) (hs : 1 ≤ s)
    {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E]
    (ρ : Representation ℂ G E) [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (ψ : (Fin 8 → Equiv.Perm (Fin s)) →* G)
    (ν : G → ℝ) (hν : ∀ g, 0 ≤ ν g) (h1 : ∑ g, ν g = 1)
    (hcoset : ∀ (i : Fin 8) g,
      ∑ h : Equiv.Perm (Fin s), ν (g * ψ (Pi.mulSingle i h)) ≤
        4 * (Fintype.card (Equiv.Perm (Fin s)) : ℝ) / Fintype.card G) :
    ‖LinearMap.toContinuousLinearMap (integrated ρ (fun g => (ν g : ℂ)))‖ ≤
      Real.sqrt (32 * C1) * (Module.finrank ℂ E : ℝ) ^ (-5 / 16 : ℝ) := by sorry
