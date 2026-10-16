-- Prove2me | Theorems.Thm_OAI_GAD_blockLogDet_scalar
-- name    : OAI.GAD.blockLogDet_scalar
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:21:28.321817+00:00
-- url     : https://prove2.me/theorems/46d596c9-e898-4ad8-a04f-1bdefc5454ff
-- title:
--   Block log-determinant functional for $1\times 1$ matrices
-- statement:
--   For finite index sets $\iota,\kappa$ and complex matrices $Z\in\mathbb{C}^{\iota\times\kappa}$, $D\in\mathbb{C}^{\iota\times\iota}$, $E\in\mathbb{C}^{\kappa\times\kappa}$, define the block log-determinant functional
--   $$\Lambda(Z;D,E)=\log\bigl|\det(D+ZE^{-1}Z^*)\bigr|-\log\bigl|\det D\bigr|.$$
--   Let $q\ge0$, $d>0$ and $e>0$ be real numbers, and regard $\sqrt q$, $d$ and $e$ as $1\times1$ complex matrices. Then
--
--   $$
--   \Lambda\bigl(\sqrt q;\,d,\,e\bigr)=\log\Bigl(1+\frac{q}{de}\Bigr).
--   $$
--
--   Since $\Lambda(Z;D,E)$ is jointly convex in $(D,E)$ on pairs of positive definite matrices, this identity shows that $(d,e)\mapsto\log(1+q/(de))$ is convex on $(0,\infty)^2$ for every $q\ge0$. That scalar convexity is what yields concavity, and then superadditivity, of the scalar entropy deficit.
--
--   **Formalization Note** The $1\times1$ matrices are `Matrix.diagonal` over `Fin 1`, and $\Lambda$ is `blockLogDet`, which uses the complex modulus and Mathlib's matrix inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/ScalarDeficit.lean#L108-L134

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Pinching
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_GramMatrices
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_ScalarDeficit

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open scoped BigOperators Topology
open Filter Set
open scoped BigOperators ComplexOrder MatrixOrder Topology
open scoped BigOperators ComplexOrder
open Matrix Set

theorem OAI.GAD.blockLogDet_scalar {q d e : ℝ} (hq : 0 ≤ q) (hd : 0 < d) (he : 0 < e) :
    blockLogDet (Matrix.diagonal (fun _ : Fin 1 ↦ (Real.sqrt q : ℂ)))
      (Matrix.diagonal (fun _ ↦ (d : ℂ))) (Matrix.diagonal (fun _ ↦ (e : ℂ))) =
      Real.log (1 + q/(d*e)) := by sorry
