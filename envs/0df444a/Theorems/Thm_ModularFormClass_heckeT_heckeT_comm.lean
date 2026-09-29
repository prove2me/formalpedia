-- Prove2me | Theorems.Thm_ModularFormClass_heckeT_heckeT_comm
-- name    : ModularFormClass.heckeT_heckeT_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/44b9a042-0038-5d3e-b7e5-70f8a32ddeeb
-- title:
--   Hecke translates Tₚ, T_q commute for coprime p,q
-- statement:
--   Let $F$ be a type of functions on the upper half-plane $\mathbb{H}$ with values in $\mathbb{C}$ (via a `FunLike` structure), let $\Gamma$ be a subgroup of $\mathrm{GL}_2(\mathbb{R})$ and $k$ an integer, and suppose $F$ is a class of modular forms of weight $k$ for $\Gamma$ (`ModularFormClass F Γ k`, so in particular each element is holomorphic on $\mathbb{H}$, weight-$k$ invariant under $\Gamma$ and bounded at the cusps). Let $f : F$, and assume that $1$ belongs to $\Gamma$`.strictPeriods`, the set of strict real periods of $\Gamma$; this hypothesis supplies the $1$-periodicity of $f \circ$ `ofComplex` and, via the fact that $\infty$ is then a cusp of $\Gamma$, the boundedness of $f$ at $i\infty$. Let $p, q$ be coprime natural numbers. For a function $g$ on $\mathbb{H}$ write $\mathrm{heckeT}\,k\,p\,g = \sum_{j < p} g \mid_k \mathrm{heckeMatrix}\,p\,j + g \mid_k \mathrm{heckeDiagMatrix}\,p$, where $\mid_k$ is the weight-$k$ slash action, the $\mathrm{heckeMatrix}\,p\,j$ ($0 \le j < p$) are the matrices used for the sum part, and $\mathrm{heckeDiagMatrix}\,p$ is the identity if $p = 0$ and otherwise the upper triangular element `upperTriangularGL p 0 1` of $\mathrm{GL}_2(\mathbb{R})$. The conclusion is the equality of functions $\mathbb{H} \to \mathbb{C}$: $\mathrm{heckeT}\,k\,p(\mathrm{heckeT}\,k\,q\,f) = \mathrm{heckeT}\,k\,q(\mathrm{heckeT}\,k\,p\,f)$. No modularity of the Hecke translates themselves is asserted or required.
--
--   This is the commutativity of the Hecke operators $T_p$ and $T_q$ at coprime indices, in the concrete form of an identity between the Hecke translates of the underlying function on $\mathbb{H}$. It is the analytic input for the corresponding statements about the linear Hecke operators on spaces of modular and cusp forms, [`ModularForm.heckeTLin_comm`](thm.html#ModularForm.heckeTLin_comm) and [`CuspForm.heckeTLin_comm`](thm.html#CuspForm.heckeTLin_comm), and thence for the existence of simultaneous eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularFormClass_heckeT_heckeT_comm.lean

import Mathlib
import Definitions.Def_ModularForm_HeckeOperator
import Definitions.Def_FLTPrelim_Modularity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularFormClass.heckeT_heckeT_comm {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) {p q : ℕ} (hpq : Nat.Coprime p q) : ModularForm.heckeT k p (ModularForm.heckeT k q ⇑f) = ModularForm.heckeT k q (ModularForm.heckeT k p ⇑f) := by sorry
