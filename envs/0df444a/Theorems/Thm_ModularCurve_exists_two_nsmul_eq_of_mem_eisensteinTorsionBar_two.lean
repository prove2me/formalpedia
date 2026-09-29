-- Prove2me | Theorems.Thm_ModularCurve_exists_two_nsmul_eq_of_mem_eisensteinTorsionBar_two
-- name    : ModularCurve.exists_two_nsmul_eq_of_mem_eisensteinTorsionBar_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/fd006ed1-4eba-5a4e-bade-ce6030245e9d
-- title:
--   2-divisibility of the Eisenstein P-power torsion at 2
-- statement:
--   Let $p$ be a prime. Write $J =$ `JZero p`, the degree-zero Picard group $\mathrm{Pic}^0$ of the modular function field `modularFunctionFieldBar p` over $\overline{\mathbf Q}$, regarded as a module over the Hecke polynomial ring `HeckeAlg` $= \mathbf Z[X_\ell : \ell \text{ prime}]$ via `heckeModuleBar p` (the action obtained by substituting the Hecke operators when they commute, and the action through substitution of $0$ otherwise). Let $\mathfrak P =$ `eisensteinMaximalIdeal p 2` be the ideal of `HeckeAlg` consisting of those polynomials whose image under `eisensteinEval p` lies in the ideal $2\mathbf Z$, and for $M \in \mathbf N$ let `eisensteinTorsionBar p 2 M` be the additive subgroup of $J$ underlying the submodule of elements killed by every element of $\mathfrak P^M$. The assertion is: for every $M \in \mathbf N$ and every $x$ in `eisensteinTorsionBar p 2 M` there exist $M' \in \mathbf N$ and $y$ in `eisensteinTorsionBar p 2 M'` with $2 \bullet y = x$. Thus the union over $M$ of the $\mathfrak P^M$-torsion subgroups of $J$ is $2$-divisible as a group, the exponent $M'$ being allowed to depend on $x$.
--
--   The Eisenstein $\mathfrak P$-power torsion of $J_0(p)(\overline{\mathbf Q})$ at residue characteristic $2$ is $2$-divisible inside itself; this is the divisibility input needed to build compatible $2$-adic sequences of Eisenstein torsion points. It is used in [`ModularCurve.exists_tateModule_apply_eq_of_mem_eisensteinTorsionBar_two`](thm.html#ModularCurve.exists_tateModule_apply_eq_of_mem_eisensteinTorsionBar_two), which realises such points in the Tate module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_two_nsmul_eq_of_mem_eisensteinTorsionBar_two.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_two_nsmul_eq_of_mem_eisensteinTorsionBar_two
    (p : ℕ) [Fact p.Prime] :
    ∀ M : ℕ, ∀ x ∈ eisensteinTorsionBar p 2 M,
      ∃ M' : ℕ, ∃ y ∈ eisensteinTorsionBar p 2 M', 2 • y = x := by sorry
