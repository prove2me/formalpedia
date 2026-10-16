-- Prove2me | Theorems.Thm_OAI_GAD_convexOn_blockLogDet
-- name    : OAI.GAD.convexOn_blockLogDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:14:07.869234+00:00
-- url     : https://prove2.me/theorems/dc5d1116-a2e7-43c0-ab8d-8d862de64241
-- title:
--   Joint convexity of $(D,E)\mapsto\log|\det(D+ZE^{-1}Z^{*})|-\log|\det D|$ on pairs of positive definite matrices
-- statement:
--   Let $\iota$ and $\kappa$ be finite index sets and let $Z\in\mathbb{C}^{\iota\times\kappa}$ be an arbitrary rectangular complex matrix, with conjugate transpose $Z^{*}$. For square matrices $D\in\mathbb{C}^{\iota\times\iota}$ and $E\in\mathbb{C}^{\kappa\times\kappa}$ define
--   $$F_Z(D,E)=\log\bigl|\det\bigl(D+ZE^{-1}Z^{*}\bigr)\bigr|-\log\bigl|\det D\bigr| ,$$
--   using natural logarithms of moduli of complex determinants. Let $\mathcal P_{\iota,\kappa}$ be the set of pairs $(D,E)$ in which $D$ and $E$ are both positive definite, inside the real vector space of pairs of complex matrices. Then $\mathcal P_{\iota,\kappa}$ is convex and $F_Z$ is jointly convex on it: for all $(D_1,E_1),(D_2,E_2)\in\mathcal P_{\iota,\kappa}$ and all $a,b\ge0$ with $a+b=1$,
--
--   $$
--   F_Z\bigl(aD_1+bD_2,\;aE_1+bE_2\bigr)\;\le\;a\,F_Z(D_1,E_1)+b\,F_Z(D_2,E_2).
--   $$
--
--   This is the main log-determinant convexity lemma of the development, valid for all finite rectangular block sizes. In the analysis of the generalized amplitude-damping channel it is used to show that this block log-determinant expression does not increase under pinching, and, specialized to $1\times1$ blocks, to obtain convexity of scalar deficit functions.
--
--   **Formalization Note** The statement is `ConvexOn ℝ {p | p.1.PosDef ∧ p.2.PosDef} (fun p ↦ blockLogDet Z p.1 p.2)` on `Matrix ι ι ℂ × Matrix κ κ ℂ`, where `blockLogDet Z D E = Real.log ‖(D + Z * E⁻¹ * Zᴴ).det‖ - Real.log ‖D.det‖`. On the domain $E$ is invertible, so `E⁻¹` is the genuine inverse.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean#L161-L178

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_LogDetConvexity

open OAI OAI.GAD
universe u_1 u_2 u_3
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open scoped ComplexOrder MatrixOrder
open Matrix Set
open scoped ComplexOrder MatrixOrder
open Matrix Set
variable {ι : Type u_2} {κ : Type u_3} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

theorem OAI.GAD.convexOn_blockLogDet (Z : Matrix ι κ ℂ) :
    ConvexOn ℝ {p : Matrix ι ι ℂ × Matrix κ κ ℂ | p.1.PosDef ∧ p.2.PosDef}
      (fun p ↦ blockLogDet Z p.1 p.2) := by sorry
