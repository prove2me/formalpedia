-- Prove2me | Theorems.Thm_OAI_GAD_sequential_decoder_bound
-- name    : OAI.GAD.sequential_decoder_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:55:56.432868+00:00
-- url     : https://prove2.me/theorems/f7240349-564e-4104-8cfa-6534168304c0
-- title:
--   Sequential decoder with a global pre-test: a POVM with an explicit error bound
-- statement:
--   Let $\iota$ be a finite index set and consider complex $\iota\times\iota$ matrices, i.e. operators on $\mathbb{C}^\iota$. An orthogonal projection is a matrix $\Pi$ with $\Pi^{*}=\Pi$ and $\Pi^2=\Pi$; a state is a positive semidefinite matrix of trace one; a POVM with $M$ outcomes is a family $D_1,\dots,D_M$ of positive semidefinite matrices with $\sum_mD_m=I$. Let $M\ge1$, let $P$ and $Q_1,\dots,Q_M$ be orthogonal projections, and let $\rho_1,\dots,\rho_M$ be states.
--
--   **Theorem.** There is a POVM $(D_m)_{m=1}^M$ such that for every $m\in\{1,\dots,M\}$
--
--   $$
--   1-\operatorname{tr}(D_m\rho_m)\le9\bigl(1-\operatorname{tr}(P\rho_m)\bigr)+8\bigl(1-\operatorname{tr}(Q_m\rho_m)\bigr)+4\sum_{j\ne m}\operatorname{tr}\bigl(Q_j\,P\rho_mP\bigr).
--   $$
--
--   The left-hand side is the probability of decoding message $m$ incorrectly when $\rho_m$ is received. The bound controls it by the probability that $\rho_m$ fails a global test $P$, the probability that it fails its own test $Q_m$, and the probabilities that the projected state $P\rho_mP$ passes the wrong tests $Q_j$. The POVM is a sequential decoder preceded by the global test: it first applies $P$ and then tests $Q_1,Q_2,\dots$ in turn. In packing-type achievability proofs $P$ is a typical projector of the average output and $Q_m$ a conditionally typical projector of codeword $m$; averaging this bound over random codebooks produces codes with small error.
--
--   **Formalization Note** Messages are indexed by `Fin M` and the tests are performed in the order of the indices; `IsProjection` means Hermitian and idempotent and `IsState` means positive semidefinite with trace $1$. The traces appear as real parts such as `(D m * A m).trace.re`; these traces are real anyway, being traces of products of two positive semidefinite matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/SequentialDecoder.lean#L102-L157

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
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalSets
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_TypicalProjectors
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_SequentialDecoder

open OAI OAI.GAD
universe u_1
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.sequential_decoder_bound {M : ℕ} (hM : 0 < M) (P : Matrix ι ι ℂ) (hP : IsProjection P)
    (Q A : Fin M → Matrix ι ι ℂ) (hQ : ∀ m, IsProjection (Q m)) (hA : ∀ m, IsState (A m)) :
    ∃ D : Fin M → Matrix ι ι ℂ, (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      ∀ m, 1-(D m*A m).trace.re ≤
        9*(1-(P*A m).trace.re)+8*(1-(Q m*A m).trace.re)+
          4*∑ j : Fin M, if j=m then 0 else (Q j*(P*A m*P)).trace.re := by sorry
