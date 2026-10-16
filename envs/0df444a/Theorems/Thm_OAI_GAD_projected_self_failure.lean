-- Prove2me | Theorems.Thm_OAI_GAD_projected_self_failure
-- name    : OAI.GAD.projected_self_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:48:18.270363+00:00
-- url     : https://prove2.me/theorems/295711e6-6a8c-4468-8495-2cab1fee6dd0
-- title:
--   Failure of a projection test after an arbitrary preliminary operator
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets. For a complex $\iota\times\kappa$ matrix $X$ write $\|X\|^2=\operatorname{Re}\operatorname{tr}(XX^{*})=\sum_{i,k}|X_{ik}|^2$ for its squared Frobenius norm. An orthogonal projection on $\mathbb{C}^\iota$ is a complex $\iota\times\iota$ matrix $Q$ with $Q^{*}=Q$ and $Q^2=Q$. Let $P$ be an arbitrary complex $\iota\times\iota$ matrix, $Q$ an orthogonal projection on $\mathbb{C}^\iota$, and $F$ a complex $\iota\times\kappa$ matrix.
--
--   **Theorem.**
--
--   $$
--   \|PF-QPF\|^2\le2\,\|F-QF\|^2+2\,\|F-PF\|^2 .
--   $$
--
--   When $P$ is also an orthogonal projection and $FF^{*}=\rho$ is a quantum state, $\|F-QF\|^2=1-\operatorname{tr}(Q\rho)$ and $\|F-PF\|^2=1-\operatorname{tr}(P\rho)$ are the probabilities that $\rho$ fails the tests $Q$ and $P$, and the left-hand side $\operatorname{tr}\bigl((I-Q)P\rho P\bigr)$ is the probability that the state after passing the test $P$ (left unnormalized) fails the test $Q$. The inequality says that a preliminary projection cannot spoil a later test by more than twice the sum of the two failure probabilities. It is used for a sequential decoder preceded by a global typical-subspace test.
--
--   **Formalization Note** `IsProjection Q` means Hermitian and idempotent, and `mass` is the squared Frobenius norm. No hypothesis on $P$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialMatrices.lean#L96-L108

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

theorem OAI.GAD.projected_self_failure {P Q : Matrix ι ι ℂ} (hQ : IsProjection Q)
    (F : Matrix ι κ ℂ) : mass (P*F-Q*(P*F)) ≤ 2*mass (F-Q*F)+2*mass (F-P*F) := by sorry
