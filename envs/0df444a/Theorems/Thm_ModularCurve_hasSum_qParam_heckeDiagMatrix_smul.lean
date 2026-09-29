-- Prove2me | Theorems.Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul
-- name    : ModularCurve.hasSum_qParam_heckeDiagMatrix_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/2911f1d3-670a-54c1-928f-273cc0b88142
-- title:
--   q_ℓ-expansion of F(ℓτ) is A(q^{ℓ^2})
-- statement:
--   Let $\ell$ be a nonzero natural number, let $A$ be a formal Laurent series over $\mathbb{C}$ (a Hahn series indexed by $\mathbb{Z}$), let $F\colon\mathfrak{H}\to\mathbb{C}$ be a function on the upper half-plane, and assume that for every $\tau\in\mathfrak{H}$ the family $m\mapsto A.\mathrm{coeff}\,m\cdot q_1(\tau)^m$, indexed by $m\in\mathbb{Z}$, is summable with sum $F(\tau)$, where $q_h(\tau)=\mathrm{e}^{2\pi\mathrm{i}\tau/h}$ is `Function.Periodic.qParam h` and the powers are integer powers. Then for every $\tau\in\mathfrak{H}$ the family $m\mapsto(\mathrm{qExpand}_{\mathbb{C}}(\ell\cdot\ell)\,A).\mathrm{coeff}\,m\cdot q_\ell(\tau)^m$, indexed by $m\in\mathbb{Z}$, is summable with sum $F(\mathrm{heckeDiagMatrix}\,\ell\cdot\tau)$. Here [`ModularCurve.qExpand N`](def/ModularCurve_X0.html#L25) is the ring endomorphism of Laurent series obtained by pushing the index set forward along the injective, order-preserving map $m\mapsto N\,m$ of $\mathbb{Z}$, i.e. the substitution $q\mapsto q^{N}$: its coefficient at $N\,m$ is $A.\mathrm{coeff}\,m$ and its coefficient at an index not divisible by $N$ is $0$; and [`ModularForm.heckeDiagMatrix ℓ`](def/ModularForm_HeckeOperator.html#L21) is, for $\ell\neq 0$, the element $\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$ of $\mathrm{GL}_2(\mathbb{R})$ (and $1$ if $\ell=0$), acting on $\mathfrak{H}$ by Möbius transformations, so that the right-hand side is $F(\ell\tau)$.
--
--   This is the statement that a function whose $q$-expansion at period $1$ is $A(q)$ has $q_\ell$-expansion $A(q^{\ell^2})$ after composition with $\tau\mapsto\ell\tau$, i.e. the expansion attached to the coset representative $\begin{pmatrix}\ell&0\\0&1\end{pmatrix}$ among the matrices of determinant $\ell$. Together with the expansions of $\tau\mapsto F((\tau+b)/\ell)$ it supplies the $q_\ell$-expansions of all $\ell+1$ Hecke coset transforms used in the construction of the modular polynomial; it is cited in the treatment of the generated modular polynomial, of the Fricke involution and of integrality of $j(q)$-adjunctions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasSum_qParam_heckeDiagMatrix_smul.lean

import Mathlib.Analysis.Complex.UpperHalfPlane.Exp
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularForm_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasSum_qParam_heckeDiagMatrix_smul (ℓ : ℕ) [NeZero ℓ] (A : LaurentSeries ℂ) (F : UpperHalfPlane → ℂ) (hA : ∀ τ : UpperHalfPlane, HasSum (fun m : ℤ => A.coeff m * Function.Periodic.qParam 1 (τ : ℂ) ^ m) (F τ)) (τ : UpperHalfPlane) : HasSum (fun m : ℤ => (ModularCurve.qExpand ℂ (ℓ * ℓ) A).coeff m * Function.Periodic.qParam ℓ (τ : ℂ) ^ m) (F (ModularForm.heckeDiagMatrix ℓ • τ)) := by sorry
