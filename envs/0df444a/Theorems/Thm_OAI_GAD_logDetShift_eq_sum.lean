-- Prove2me | Theorems.Thm_OAI_GAD_logDetShift_eq_sum
-- name    : OAI.GAD.logDetShift_eq_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:17:46.434993+00:00
-- url     : https://prove2.me/theorems/49450831-6822-4fe4-b120-cf216d4f3bdd
-- title:
--   Spectral formula for the log-determinant $\log|\det(I+rA)|$ of a positive semidefinite matrix
-- statement:
--   Let $\iota$ be a finite index set, let $A\in\mathbb{C}^{\iota\times\iota}$ be positive semidefinite with eigenvalues $\lambda_i\ge0$ ($i\in\iota$, counted with multiplicity), and let $r\ge0$ be real. Then
--
--   $$
--   \log\bigl|\det(I+rA)\bigr|=\sum_{i\in\iota}\log(1+r\lambda_i).
--   $$
--
--   Here $|\cdot|$ is the modulus of a complex number; in fact $\det(I+rA)=\prod_i(1+r\lambda_i)\ge1$ is a positive real number. The function $r\mapsto\log|\det(I+rA)|$ is the logarithmic resolvent determinant of $A$; this formula expresses it through the spectrum, and it is the bridge between matrix log-determinant inequalities and the scalar spectral sums used to compare entropies.
--
--   **Formalization Note** The left-hand side is `logDetShift r A`, defined as `Real.log ‖(1 + r • A).det‖`; the eigenvalues are `hA.isHermitian.eigenvalues`, a real-valued function on $\iota$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean#L113-L137

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetEntropy

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
open Matrix
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.logDetShift_eq_sum {A : Matrix ι ι ℂ} (hA : A.PosSemidef)
    {r : ℝ} (hr : 0 ≤ r) :
    logDetShift r A = ∑ i, Real.log (1 + r * hA.isHermitian.eigenvalues i) := by sorry
