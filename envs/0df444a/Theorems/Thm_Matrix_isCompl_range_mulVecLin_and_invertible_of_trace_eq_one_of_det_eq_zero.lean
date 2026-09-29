-- Prove2me | Theorems.Thm_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
-- name    : Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.429051+00:00
-- url     : https://prove2.me/theorems/dcccb0ba-f99d-5e2c-900b-7a5fbeaa4aae
-- title:
--   Trace-one, determinant-zero 2×2 matrices are rank-one projectors
-- statement:
--   Let $R$ be a commutative ring and let $e \in M_2(R)$ be a $2 \times 2$ matrix, indexed by `Fin 2`, whose trace is $1$ and whose determinant is $0$. Then three things hold simultaneously. First, $e$ is idempotent: $e \cdot e = e$. Second, writing `Matrix.mulVecLin e` for the $R$-linear endomorphism $v \mapsto e v$ of $R^{\mathrm{Fin}\,2}$, the two submodules $P = \operatorname{range}(v \mapsto e v)$ and $Q = \operatorname{range}(v \mapsto (1 - e) v)$ are complementary in $R^{\mathrm{Fin}\,2}$ in the sense of `IsCompl`, i.e. $P \sqcap Q = \bot$ and $P \sqcup Q = \top$, so that $R^{\mathrm{Fin}\,2} = P \oplus Q$. Third, each of $P$ and $Q$, regarded as an $R$-module via the coercion of the submodule to a type, is an invertible $R$-module in the sense of `Module.Invertible`. No hypothesis beyond commutativity of $R$ and the two scalar conditions $\operatorname{tr} e = 1$, $\det e = 0$ is imposed; in particular $R$ is not assumed local, Noetherian, or nonzero.
--
--   This is the elementary statement that a $2 \times 2$ matrix of trace one and determinant zero over a commutative ring is a projector of constant rank one, splitting the free module of rank two into two complementary invertible (rank-one projective) submodules. It is used in the analysis of formal modules over quaternionic data, being cited in the proofs that such modules are special and of height four.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Matrix_isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Matrix.isCompl_range_mulVecLin_and_invertible_of_trace_eq_one_of_det_eq_zero
    {R : Type*} [CommRing R] (e : Matrix (Fin 2) (Fin 2) R) (htr : e.trace = 1) (hdet : e.det = 0) :
    e * e = e ∧
      IsCompl (LinearMap.range (Matrix.mulVecLin e)) (LinearMap.range (Matrix.mulVecLin (1 - e))) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin e)) ∧
      Module.Invertible R ↥(LinearMap.range (Matrix.mulVecLin (1 - e))) := by sorry
