-- Prove2me | Theorems.Thm_OAI_GAD_entropy_le_of_logDetShift_le
-- name    : OAI.GAD.entropy_le_of_logDetShift_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:18:15.042029+00:00
-- url     : https://prove2.me/theorems/b34ab227-4db5-47f9-91fd-91a6bbbe989f
-- title:
--   Log-determinant domination of resolvents implies entropy domination
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets, possibly of different sizes, and let $A\in\mathbb{C}^{\iota\times\iota}$ and $B\in\mathbb{C}^{\kappa\times\kappa}$ be positive semidefinite. For a positive semidefinite matrix $M$ with eigenvalues $\lambda_j(M)$ let $S(M)=\sum_j\eta(\lambda_j(M))$, $\eta(x)=-x\log x$, be its von Neumann entropy, with no trace normalization. Assume that $\operatorname{Tr}A=\operatorname{Tr}B$ and that $\log|\det(I_\iota+rA)|\le\log|\det(I_\kappa+rB)|$ for every real $r>0$. Then
--
--   $$
--   S(A)\le S(B).
--   $$
--
--   Thus a comparison of the resolvent log-determinants for all $r>0$, together with equality of traces, implies a comparison of entropies, even between matrices of different sizes. This is how matrix entropy inequalities in this development are derived from log-determinant inequalities, which are often easier to obtain from Schur complements and convexity; applying the theorem in both directions shows that equal traces and equal log-determinants for all $r>0$ force equal entropies.
--
--   **Formalization Note** The trace hypothesis is stated for real parts, `A.trace.re = B.trace.re` (both traces are real). The log-determinants are `logDetShift r A = Real.log ‖(1 + r • A).det‖`, and `entropy` is the real part of the trace of `cfc Real.negMulLog`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetEntropy.lean#L139-L166

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

theorem OAI.GAD.entropy_le_of_logDetShift_le {κ : Type u_3} [Fintype κ] [DecidableEq κ]
    {A : Matrix ι ι ℂ} {B : Matrix κ κ ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (htrace : A.trace.re = B.trace.re)
    (hlog : ∀ r : ℝ, 0 < r → logDetShift r A ≤ logDetShift r B) :
    entropy A ≤ entropy B := by sorry
