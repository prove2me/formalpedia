-- Prove2me | Theorems.Thm_OAI_Thorp_Fourier_coefficient_second_moment
-- name    : OAI.Thorp.Fourier.coefficient_second_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:37:48.435607+00:00
-- url     : https://prove2.me/theorems/0521781c-88e0-4fdb-93d6-4c2fca41769c
-- title:
--   Schur orthogonality: mean square of a matrix coefficient of an irreducible unitary representation
-- statement:
--   Let $G$ be a finite group and $E$ a finite-dimensional complex inner product space of dimension $d=\dim_{\mathbb{C}}E\ne 0$, with inner product $\langle\cdot,\cdot\rangle$ and norm $\|\cdot\|$. Let $\rho$ be an irreducible representation of $G$ on $E$ that is unitary, i.e. $\langle\rho(g)x,\rho(g)y\rangle=\langle x,y\rangle$ for all $g\in G$ and $x,y\in E$. Then for all vectors $v,w\in E$,
--
--   $$
--   \frac{1}{|G|}\sum_{g\in G}\big|\langle w,\rho(g)v\rangle\big|^2=\frac{\|v\|^2\,\|w\|^2}{d}.
--   $$
--
--   This is the diagonal case of the Schur orthogonality relations for matrix coefficients. Probabilistically, if $g$ is uniformly distributed on $G$, the matrix coefficient $\langle w,\rho(g)v\rangle$ of unit vectors has mean square exactly $1/d$, so it is typically of size $d^{-1/2}$. Such second-moment identities are the input for bounding the operator norm of averages $\sum_g\nu(g)\rho(g)$ by negative powers of the dimension.
--
--   **Formalization Note** The hypotheses are `[Representation.IsIrreducible ρ]`, the unitarity condition `hu`, and `Module.finrank ℂ E ≠ 0`; the inner product `⟪x, y⟫_ℂ` is conjugate-linear in its first argument (which does not affect the absolute values above).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpShuffle/Reynolds.lean#L93-L113

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

open OAI OAI.Thorp OAI.Thorp.Fourier
universe uG uV uW uE uI
open scoped BigOperators ComplexConjugate InnerProductSpace
open Filter Topology
open scoped BigOperators ComplexConjugate InnerProductSpace
open scoped Classical
variable {G : Type uG} [Group G] [Fintype G]
variable {V : Type uV} {W : Type uW} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

theorem OAI.Thorp.Fourier.coefficient_second_moment (ρ : Representation ℂ G E)
    [Representation.IsIrreducible ρ]
    (hu : ∀ g x y, ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hE : Module.finrank ℂ E ≠ 0) (v w : E) :
    (Fintype.card G : ℝ)⁻¹ * ∑ g : G, ‖⟪w, ρ g v⟫_ℂ‖ ^ 2 =
      ‖v‖ ^ 2 * ‖w‖ ^ 2 / Module.finrank ℂ E := by sorry
