-- Prove2me | Theorems.Thm_OAI_GAD_frobVector_inner
-- name    : OAI.GAD.frobVector_inner
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:29:50.695345+00:00
-- url     : https://prove2.me/theorems/3ad5915e-38e0-4a79-9138-ff6cbe8ec8ab
-- title:
--   The real Frobenius inner product of two complex matrices equals $\operatorname{Re}\operatorname{Tr}(A^*B)$
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets. For a matrix $A\in\mathbb{C}^{\iota\times\kappa}$ let $\mathrm{vec}(A)$ be the same array regarded as a vector of the Euclidean space $\ell^2(\iota\times\kappa)$ over $\mathbb{C}$, with coordinates $\mathrm{vec}(A)_{(i,k)}=A_{ik}$. On this space use the real inner product $\langle x,y\rangle_{\mathbb{R}}=\operatorname{Re}\sum_{(i,k)}\overline{x_{ik}}\,y_{ik}$. Then for all $A,B\in\mathbb{C}^{\iota\times\kappa}$,
--   $$
--   \langle\mathrm{vec}(A),\mathrm{vec}(B)\rangle_{\mathbb{R}}=\operatorname{Re}\operatorname{Tr}\big(A^{*}B\big),
--   $$
--   where $A^{*}$ is the conjugate transpose of $A$.
--
--   In particular $\|\mathrm{vec}(A)\|^2=\operatorname{Tr}(AA^{*})$, so the Hilbert–Schmidt (Frobenius) geometry of rectangular complex matrices is the Euclidean geometry of their vectorizations. This makes Pythagoras, polarization and orthogonal-projection arguments available for Gram factors of quantum states, where $\operatorname{Re}\operatorname{Tr}(A^{*}B)$ measures the overlap of two factors.
--
--   **Formalization Note** $\mathrm{vec}(A)$ is `frobVector A`, an element of `EuclideanSpace ℂ (ι × κ)`, and the left-hand side is Mathlib's real inner product, the real part of the complex inner product (which is conjugate-linear in the first argument).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/EntropyContinuity.lean#L31-L48

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

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5 u_6 u_7
open scoped BigOperators ComplexOrder MatrixOrder InnerProductSpace
open Matrix
variable {ι : Type u_1} {κ : Type u_2} [Fintype ι] [Fintype κ]

theorem OAI.GAD.frobVector_inner (A B : Matrix ι κ ℂ) :
    ⟪frobVector A,frobVector B⟫_ℝ=(Aᴴ*B).trace.re := by sorry
