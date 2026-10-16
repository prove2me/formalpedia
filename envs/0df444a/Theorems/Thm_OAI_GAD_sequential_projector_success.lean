-- Prove2me | Theorems.Thm_OAI_GAD_sequential_projector_success
-- name    : OAI.GAD.sequential_projector_success
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:47:34.865451+00:00
-- url     : https://prove2.me/theorems/4be6a9e7-8317-4215-a2c7-772b260c4e15
-- title:
--   Sequential projective union bound for matrices in Frobenius norm
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets. For a complex $\iota\times\kappa$ matrix $X$ write $\|X\|^2=\operatorname{Re}\operatorname{tr}(XX^{*})=\sum_{i,k}|X_{ik}|^2$ for its squared Frobenius norm. An orthogonal projection on $\mathbb{C}^\iota$ is a complex $\iota\times\iota$ matrix $Q$ with $Q^{*}=Q$ and $Q^2=Q$. Let $(Q_k)_{k\ge0}$ be a sequence of orthogonal projections on $\mathbb{C}^\iota$ and define the rejection products
--
--   $$
--   R_0=I,\qquad R_{k+1}=(I-Q_k)\,R_k,\qquad\text{so that}\quad R_m=(I-Q_{m-1})\cdots(I-Q_1)(I-Q_0).
--   $$
--
--   **Theorem.** For every complex $\iota\times\kappa$ matrix $Y$ and every $m\in\mathbb{N}$,
--
--   $$
--   \|Y\|^2-\|Q_mR_mY\|^2\le4\Bigl(\|Y-Q_mY\|^2+\sum_{j=0}^{m-1}\|Q_jY\|^2\Bigr).
--   $$
--
--   When $YY^{*}=\rho$ is a quantum state, $\|Q_mR_mY\|^2=\operatorname{tr}(R_m^{*}Q_mR_m\,\rho)$ is the probability that the sequential measurement which tests $Q_0,Q_1,\dots$ in turn rejects the first $m$ tests and accepts at test $m$, while $\|Y-Q_mY\|^2=1-\operatorname{tr}(Q_m\rho)$ and $\|Q_jY\|^2=\operatorname{tr}(Q_j\rho)$. The theorem is thus a sequential (non-commutative) union bound: the probability of not stopping at $m$ is at most four times the sum of the probability that the correct test fails and the probabilities that the earlier, wrong tests accept. It is the basic estimate behind sequential decoders for classical-quantum channels.
--
--   **Formalization Note** `IsProjection Q` means that `Q` is Hermitian and `Q * Q = Q`; `mass X` is the squared Frobenius norm $\|X\|^2$ and `rejectProduct Q m` is $R_m$. The projections are indexed by all natural numbers, but only $Q_0,\dots,Q_m$ enter the statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean#L58-L88

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ThermalEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TensorEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PureRecursion
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_StateEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EntropyContinuity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_BlockFactors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Naimark
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_HolevoInformation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_OutputEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_EnsembleBounds
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseStates
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_PhaseProducts
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_CapacityConverse
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialMatrices

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem OAI.GAD.sequential_projector_success (Q : ℕ → Matrix ι ι ℂ)
    (hQ : ∀ k, IsProjection (Q k)) (Y : Matrix ι κ ℂ) (m : ℕ) :
    mass Y-mass (Q m*rejectProduct Q m*Y) ≤
      4*(mass (Y-Q m*Y)+∑ j ∈ Finset.range m, mass (Q j*Y)) := by sorry
