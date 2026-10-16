-- Prove2me | Theorems.Thm_OAI_GAD_convexOn_skewLogDet
-- name    : OAI.GAD.convexOn_skewLogDet
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:12:56.99131+00:00
-- url     : https://prove2.me/theorems/50770cd7-3fdc-4af0-81f4-90c80afecfba
-- title:
--   Convexity of $D\mapsto\log|\det(D+Z)|-\log|\det D|$ on positive definite matrices for skew-Hermitian $Z$
-- statement:
--   Let $\iota$ be a finite index set and let $Z\in\mathbb{C}^{\iota\times\iota}$ be skew-Hermitian, $Z^{*}=-Z$. For complex matrices $D\in\mathbb{C}^{\iota\times\iota}$ define
--   $$f_Z(D)=\log\bigl|\det(D+Z)\bigr|-\log\bigl|\det D\bigr| ,$$
--   using natural logarithms of the moduli of the (possibly non-real) complex determinants. Let $\mathcal P=\{D\in\mathbb{C}^{\iota\times\iota}:D\text{ is positive definite}\}$, viewed inside the real vector space of complex matrices. Then $\mathcal P$ is convex and $f_Z$ is convex on $\mathcal P$: for all $D,E\in\mathcal P$ and all $a,b\ge0$ with $a+b=1$,
--
--   $$
--   f_Z(aD+bE)\;\le\;a\,f_Z(D)+b\,f_Z(E).
--   $$
--
--   The function $f_Z$ measures how much the log-determinant changes under a fixed skew-Hermitian perturbation. Its convexity is the mechanism behind joint convexity of block expressions such as $\log|\det(D+ZE^{-1}Z^{*})|-\log|\det D|$ in a pair of positive definite matrices.
--
--   **Formalization Note** The statement is `ConvexOn ℝ {D | D.PosDef} (skewLogDet Z)`, which includes convexity of the domain, with `skewLogDet Z D = Real.log ‖(D + Z).det‖ - Real.log ‖D.det‖`. For positive definite $D$ both determinants are nonzero, so the convention $\log0=0$ plays no role on the domain.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/LogDetConvexity.lean#L52-L102

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
variable {ι : Type u_1} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.convexOn_skewLogDet (Z : Matrix ι ι ℂ) (hZ : Z.conjTranspose = -Z) :
    ConvexOn ℝ {D : Matrix ι ι ℂ | D.PosDef} (skewLogDet Z) := by sorry
