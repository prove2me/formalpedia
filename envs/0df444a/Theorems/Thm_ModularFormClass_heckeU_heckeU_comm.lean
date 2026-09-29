-- Prove2me | Theorems.Thm_ModularFormClass_heckeU_heckeU_comm
-- name    : ModularFormClass.heckeU_heckeU_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/f3f80576-97c9-5e28-975f-d88e7b710af9
-- title:
--   Commutativity of the Hecke operators Uₚ and U_q
-- statement:
--   Let $F$ be a type of functions on the upper half-plane $\mathbb{H}$ with values in $\mathbb{C}$ (a `FunLike` structure), let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$, let $k$ be an integer, and assume $F$ is a class of modular forms of weight $k$ for $\Gamma$ (`ModularFormClass F Γ k`). Let $f : F$, and assume $1$ belongs to `Γ.strictPeriods`, i.e. the real number $1$ is a strict period of $\Gamma$ in Mathlib's sense, so that the translation $z \mapsto z+1$ is available as a symmetry and the cusp $\infty$ is a cusp of $\Gamma$. Let $p$ and $q$ be arbitrary natural numbers. Here, for a function $g : \mathbb{H} \to \mathbb{C}$, the operator is defined by $\mathrm{heckeU}\,k\,p\,g = \sum_{j=0}^{p-1} g \mid_k \gamma_{p,j}$, the weight-$k$ slash action of the invertible real matrices $\gamma_{p,j}$ with rows $(1, j)$ and $(0, p)$ for $p \neq 0$ (and $\gamma_{0,j} = 1$, so that the empty sum makes $\mathrm{heckeU}\,k\,0$ the zero function). The conclusion is the equality of functions $\mathbb{H} \to \mathbb{C}$: $U_p(U_q \underline{f}) = U_q(U_p \underline{f})$, where $\underline{f}$ is the function underlying $f$. No primality, coprimality or positivity hypothesis on $p$ and $q$ is imposed.
--
--   This is the commutativity of the operators $U_p$ on modular forms, one ingredient in the commutativity of the Hecke algebra acting on spaces of modular forms. It is used for the corresponding statement for linear operators on cusp forms, [`CuspForm.heckeULin_comm`](thm.html#CuspForm.heckeULin_comm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_heckeU_heckeU_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.heckeU_heckeU_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (p q : ℕ) : ModularForm.heckeU k p (ModularForm.heckeU k q ⇑f) = ModularForm.heckeU k q (ModularForm.heckeU k p ⇑f) := by sorry
