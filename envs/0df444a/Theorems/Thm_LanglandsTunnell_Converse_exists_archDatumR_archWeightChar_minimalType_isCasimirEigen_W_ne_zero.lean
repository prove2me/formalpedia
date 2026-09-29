-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
-- name    : LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/e3d3e560-0fc2-5325-a142-b8aea2850e39
-- title:
--   Minimal-weight archimedean Whittaker datum for a real parameter
-- statement:
--   Let $P$ be a real archimedean parameter, i.e. an element of `RealArchParam`: either `principal` $(u_1,a_1,u_2,a_2)$ with $u_1,u_2\in\mathbb C$ and $a_1,a_2\in\mathbb Z/2$, or `discrete` $(u,k)$ with $k\ge 1$. Assume the genericity condition `hgen`: whenever $P$ is of principal type $(u_1,a_1,u_2,a_2)$ and $u_1-u_2=p$ for a nonzero integer $p$, then $a_1-a_2\neq p+1$ in $\mathbb Z/2$. The assertion is that there exist an archimedean Whittaker datum $D$ for $P$ — a structure `ArchDatumR P` consisting of a function $W$ on $2\times2$ real matrices which is smooth on the invertible locus, transforms by $\psi(x)$ under left translation by unipotents and by $\operatorname{centralChar} P(z)\,|z|$ under scaling by $z\ne 0$, together with entire zeta functions of finite order representing the zeta integrals of $W$ against the quasi-characters as the twisted archimedean $\Gamma$-factor `archFactor` of $P$ times an entire function, satisfying the local functional equation with the epsilon factor of $P$ and the prescribed decay bounds — and an integer $k_0$ such that: if $P$ is principal $(u_1,a_1,u_2,a_2)$ then $k_0\in\{0,1\}$ and $k_0\equiv a_1+a_2 \pmod 2$; if $P$ is discrete $(u,m)$ with $m\ge1$ then $k_0=m+1$; $W$ has weight $k_0$, in the sense that $W(xr)=\operatorname{archWeightChar}_{\mathbb R}(k_0)(r)\,W(x)$ for all $x\in \mathrm{GL}_2(\mathbb R)$ and all $r$ in the determinant-one row-isometry subgroup `rowIsometrySubgroup₀ ℝ`; $D$ satisfies the Casimir eigen-equation, i.e. $\operatorname{matrixCasimir} W$, namely $-\bigl(\tfrac14 H^2W-\tfrac12 HW+E\,F\,W\bigr)$ in the flow derivatives along $H$, $E$, $F$, equals $\lambda(P)\,W$ at every matrix of nonzero determinant, where $\lambda(P)=\tfrac14-((u_1-u_2)/2)^2$ in the principal case and $(1-m^2)/4$ in the discrete case; and $W$ is nonzero at some element of $\mathrm{GL}_2(\mathbb R)$.
--
--   This produces the minimal-weight archimedean Whittaker function attached to a real $\mathrm{GL}_2$-parameter, with its $\mathrm{SO}(2)$-weight and its Casimir eigenvalue, as an input to the converse-theorem construction. It is used in the Rankin–Selberg archimedean gamma-factor comparison and in the assembly of an automorphic Whittaker datum from an archimedean parameter occurring in a given class over $\mathbb Q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero.lean

import Definitions.Def_LanglandsTunnell_JLConverse
import Definitions.Def_LanglandsTunnell_ArchCasimirCompanion
import Definitions.Def_AutomorphicForm_ArchWeightChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open LanglandsTunnell LanglandsTunnell.RealArchParam LanglandsTunnell.Converse AutomorphicForm

theorem LanglandsTunnell.Converse.exists_archDatumR_archWeightChar_minimalType_isCasimirEigen_W_ne_zero
    (P : RealArchParam)
    (hgen : (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
      ∀ p : ℤ, p ≠ 0 → u₁ - u₂ = (p : ℂ) → a₁ - a₂ ≠ ((p + 1 : ℤ) : ZMod 2))) :
    ∃ (D : ArchDatumR P) (k₀ : ℤ),
      (∀ (u₁ u₂ : ℂ) (a₁ a₂ : ZMod 2), P = RealArchParam.principal u₁ a₁ u₂ a₂ →
        (k₀ = 0 ∨ k₀ = 1) ∧ ((k₀ : ZMod 2) = a₁ + a₂)) ∧
      (∀ (u : ℂ) (m : ℕ) (hm : 1 ≤ m), P = RealArchParam.discrete u m hm → k₀ = (m : ℤ) + 1) ∧
      (∀ (r : rowIsometrySubgroup₀ ℝ) (x : GL (Fin 2) ℝ),
        D.W ((x * (r : GL (Fin 2) ℝ) : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) =
          (archWeightCharℝ k₀ r : ℂ) * D.W (x : Matrix (Fin 2) (Fin 2) ℝ)) ∧
      ArchCasimir.IsCasimirEigen D ∧
      ∃ g : GL (Fin 2) ℝ, D.W g ≠ 0 := by sorry
