-- Prove2me | Theorems.Thm_OAI_GAD_exists_packed_measurement
-- name    : OAI.GAD.exists_packed_measurement
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:58:29.854151+00:00
-- url     : https://prove2.me/theorems/3ee32e6f-fd88-4e61-9de6-b7a12497d901
-- title:
--   Finite i.i.d. quantum packing lemma with a sequential decoder
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space with a fixed orthonormal basis, so that operators on $\mathcal H$ are square complex matrices, and let $\mathcal X$ be a finite alphabet. A *state* (density matrix) is a positive semidefinite matrix $A\succeq0$ with $\operatorname{tr}A=1$; an *orthogonal projection* is a Hermitian matrix $\Pi$ with $\Pi^{2}=\Pi$; and $X\preceq Y$ means that $Y-X$ is positive semidefinite.
--
--   Let $q$ be a probability vector on $\mathcal X$ ($q(x)\ge0$ and $\sum_{x}q(x)=1$), let $(A_x)_{x\in\mathcal X}$ be states, let $(Q_x)_{x\in\mathcal X}$ be orthogonal projections, let $P$ be an orthogonal projection, and write $\bar A=\sum_{x}q(x)A_x$ for the average state. Let $a,b,c,r$ be real numbers with $c\ge0$ and $r\ge0$ such that
--
--   1. $\sum_{x}q(x)\bigl(1-\operatorname{Re}\operatorname{tr}(PA_x)\bigr)\le a$;
--   2. $\sum_{x}q(x)\bigl(1-\operatorname{Re}\operatorname{tr}(Q_xA_x)\bigr)\le b$;
--   3. $\operatorname{Re}\operatorname{tr}Q_x\le r$ for every $x\in\mathcal X$ (each $Q_x$ has rank at most $r$);
--   4. $P\bar AP\preceq c\,P$, i.e. $cP-P\bar AP$ is positive semidefinite.
--
--   Then for every integer $M\ge1$ there exist codewords $x_1,\dots,x_M\in\mathcal X$ (not necessarily distinct) and a POVM $D_1,\dots,D_M$ on $\mathcal H$, that is $D_m\succeq0$ for every $m$ and $\sum_{m=1}^{M}D_m=I$, such that
--
--   $$
--   1-\frac1M\sum_{m=1}^{M}\operatorname{Re}\operatorname{tr}\bigl(D_m A_{x_m}\bigr)\;\le\;9a+8b+4Mcr .
--   $$
--
--   The left-hand side is the average probability of a decoding error when message $m$ is sent as the state $A_{x_m}$ and the receiver measures the POVM $(D_m)$. This is a non-asymptotic packing lemma: when $P$ is a typical projection of the average state and $Q_x$ is a conditional typical projection of the signal $A_x$ of an $n$-fold product source, the losses $a,b$ are small, $c$ is exponentially small and $r$ exponentially large, so any number of messages $M$ well below $1/(cr)$ can be decoded with small average error. It is the core of the direct part of the classical coding theorem for the generalized amplitude-damping channel.
--
--   **Formalization Note** The Hilbert space is $\mathbb{C}^{\iota}$ for an arbitrary finite type `ι`, the alphabet is an arbitrary finite type `α`, and messages are indexed by `Fin M`. States and projections are the predicates `IsState` and `IsProjection`. Traces of complex matrices are complex numbers and the statement uses their real parts; for the products of Hermitian matrices that occur here the traces are real anyway.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/FinitePacking.lean#L109-L180

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
universe u_1 u_2 u_3
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_2} {α : Type u_3} [Fintype ι] [Fintype α] [DecidableEq ι]

theorem OAI.GAD.exists_packed_measurement (q : α → ℝ) (hq : ∀ a, 0 ≤ q a) (hs : ∑ a, q a=1)
    (A Q : α → Matrix ι ι ℂ) (hA : ∀ a, IsState (A a)) (hQ : ∀ a, IsProjection (Q a))
    (P : Matrix ι ι ℂ) (hP : IsProjection P) {a b c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r)
    (hga : (∑ x, q x*(1-(P*A x).trace.re)) ≤ a)
    (hcb : (∑ x, q x*(1-(Q x*A x).trace.re)) ≤ b)
    (hr : ∀ x, (Q x).trace.re ≤ r)
    (hcp : (c • P-P*(∑ x, q x • A x)*P).PosSemidef)
    (M : ℕ) (hM : 0 < M) :
    ∃ (x : Fin M → α) (D : Fin M → Matrix ι ι ℂ),
      (∀ m, (D m).PosSemidef) ∧ (∑ m, D m=1) ∧
      1-(∑ m, (D m*A (x m)).trace.re)/(M:ℝ) ≤ 9*a+8*b+4*(M:ℝ)*c*r := by sorry
