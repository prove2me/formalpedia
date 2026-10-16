-- Prove2me | Theorems.Thm_OAI_GAD_blockLogDet_diagonal_real
-- name    : OAI.GAD.blockLogDet_diagonal_real
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:18:42.78377+00:00
-- url     : https://prove2.me/theorems/c88c0d30-2d3b-4d91-8177-6178fd861061
-- title:
--   Block log-determinant functional at real diagonal matrices
-- statement:
--   For finite index sets $\iota,\kappa$ and complex matrices $Z\in\mathbb{C}^{\iota\times\kappa}$, $D\in\mathbb{C}^{\iota\times\iota}$, $E\in\mathbb{C}^{\kappa\times\kappa}$, define the block log-determinant functional
--   $$\Lambda(Z;D,E)=\log\bigl|\det(D+ZE^{-1}Z^*)\bigr|-\log\bigl|\det D\bigr|.$$
--   Now let $\iota$ be a finite index set and let $z,d,e:\iota\to\mathbb{R}$ satisfy $d_i>0$ and $e_i>0$ for all $i$. For the diagonal matrices $\operatorname{diag}(z),\operatorname{diag}(d),\operatorname{diag}(e)\in\mathbb{C}^{\iota\times\iota}$,
--
--   $$
--   \Lambda\bigl(\operatorname{diag}(z);\operatorname{diag}(d),\operatorname{diag}(e)\bigr)=\sum_{i\in\iota}\log\Bigl(1+\frac{z_i^2}{d_ie_i}\Bigr).
--   $$
--
--   The functional $\Lambda$ is jointly convex in $(D,E)$ on pairs of positive definite matrices, and when $Z$ is diagonal, pinching $D$ and $E$ to their diagonals can only decrease it. This explicit diagonal evaluation turns such matrix bounds into sums of scalar logarithms, which is how log-determinant estimates for Gram matrices of block matrices are reduced to coordinatewise inequalities.
--
--   **Formalization Note** $\Lambda(Z;D,E)$ is `blockLogDet Z D E`, which uses the complex modulus and Mathlib's matrix inverse; the real vectors $z,d,e$ are coerced to complex diagonal matrices.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/GramMatrices.lean#L133-L163

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices

open OAI OAI.GAD
universe u_1 u_2 u_3 u_4 u_5
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_5} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.blockLogDet_diagonal_real (z d e : ι → ℝ) (hd : ∀ i, 0 < d i) (he : ∀ i, 0 < e i) :
    blockLogDet (Matrix.diagonal (fun i ↦ (z i : ℂ)))
      (Matrix.diagonal (fun i ↦ (d i : ℂ))) (Matrix.diagonal (fun i ↦ (e i : ℂ))) =
      ∑ i, Real.log (1+(z i)^2/(d i*e i)) := by sorry
