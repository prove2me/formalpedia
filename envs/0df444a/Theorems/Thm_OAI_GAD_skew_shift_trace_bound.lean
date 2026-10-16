-- Prove2me | Theorems.Thm_OAI_GAD_skew_shift_trace_bound
-- name    : OAI.GAD.skew_shift_trace_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T22:12:00.425521+00:00
-- url     : https://prove2.me/theorems/5f4eee5a-73b2-498f-a777-24c1cce6ba32
-- title:
--   A skew-Hermitian shift of a positive definite $D$ is invertible and decreases $\operatorname{Re}\operatorname{tr}((D^{-1}H)^2)$
-- statement:
--   Let $\iota$ be a finite index set and let $D,Z,H\in\mathbb{C}^{\iota\times\iota}$, where $D$ is positive definite, $Z$ is skew-Hermitian ($Z^{*}=-Z$) and $H$ is Hermitian. Then:
--
--   1. the matrix $D+Z$ is invertible;
--   2. the following trace inequality holds:
--
--   $$
--   \operatorname{Re}\operatorname{tr}\Bigl(\bigl((D+Z)^{-1}H\bigr)^2\Bigr)\;\le\;\operatorname{Re}\operatorname{tr}\Bigl(\bigl(D^{-1}H\bigr)^2\Bigr).
--   $$
--
--   Along a line $s\mapsto D+sH$, the second derivative of $\log|\det(D+sH)|$ at $s=0$ equals $-\operatorname{Re}\operatorname{tr}\bigl((D^{-1}H)^2\bigr)$. The inequality therefore says that this second derivative can only increase when $D$ is shifted by a fixed skew-Hermitian matrix. It is the Hessian comparison that makes $D\mapsto\log|\det(D+Z)|-\log|\det D|$ convex on positive definite matrices.
--
--   **Formalization Note** Invertibility is stated as `IsUnit (D + Z)`, inverses are Mathlib's matrix inverses, and positive definiteness is `Matrix.PosDef` (Hermitian with $x^{*}Dx>0$ for all $x\neq0$).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/AmplitudeDamping/MatrixDifferentiation.lean#L224-L273

import Mathlib
import Definitions.Def_AmplitudeDamping
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_Channel
import Definitions.Def_OAI_InformationTheory_AmplitudeDamping_MatrixDifferentiation

open OAI OAI.GAD
universe u_1 u_2
open scoped BigOperators
open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Matrix
variable {ι : Type u_2} [Fintype ι] [DecidableEq ι]

theorem OAI.GAD.skew_shift_trace_bound (D Z H : Matrix ι ι ℂ)
    (hD : D.PosDef) (hZ : Z.conjTranspose = -Z) (hH : H.IsHermitian) :
    IsUnit (D + Z) ∧
      (Matrix.trace (((D + Z)⁻¹ * H) * ((D + Z)⁻¹ * H))).re ≤
        (Matrix.trace ((D⁻¹ * H) * (D⁻¹ * H))).re := by sorry
