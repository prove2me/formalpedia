-- Prove2me | Theorems.Thm_ModularCurve_periodMap_atkinLehnerLin_apply
-- name    : ModularCurve.periodMap_atkinLehnerLin_apply
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/8f05a3e1-620a-5a5a-9b12-dd09dfdec94e
-- title:
--   Period map intertwines w_q with matrix conjugation
-- statement:
--   Let $M$ and $q$ be natural numbers with $M \neq 0$, and let $W$ be an Atkin–Lehner datum for $(M,q)$: a natural number $R$ with $M = qR$ together with integers $a, b$ satisfying $qa - Rb = 1$, whose associated integral matrix is $W.\mathrm{mat} = \begin{pmatrix} qa & b \\ qR & q\end{pmatrix}$. Let $f$ be a cusp form of weight $2$ for $\Gamma_0(M)$ and let $\gamma, \delta \in \Gamma_0(M)$ satisfy the relation $\delta \cdot W.\mathrm{mat} = W.\mathrm{mat} \cdot \gamma$ as products of $2 \times 2$ integer matrices (the elements $\gamma, \delta$ being viewed in $\mathrm{SL}_2(\mathbb{Z})$ and then as integer matrices). The assertion is that the value at $\gamma$ of the period homomorphism $\mathrm{periodMap}\ M$ applied to the image of $f$ under [`CuspForm.atkinLehnerLin W 2`](def/CuspForm_AtkinLehnerOperator.html#L41), that is the cusp form whose underlying function is the weight-$2$ slash $f \mid_2 W.\mathrm{alGL}$ by the real matrix attached to $W.\mathrm{mat}$, equals the value at $\delta$ of $\mathrm{periodMap}\ M\ f$. Here $\mathrm{periodMap}\ N\ g$ is the homomorphism $\mathrm{Additive}(\Gamma_0(N)) \to \mathbb{C}$ obtained, when some $F : \mathbb{H} \to \mathbb{C}$ has derivative $g$ at every point, tends to $0$ at $i\infty$, is a $\Gamma_0(N)$-equivariant primitive and has a limit at $i\infty$ along every $\mathrm{SL}_2(\mathbb{Z})$-translate, as the period homomorphism of such a chosen $F$, and is $0$ otherwise.
--
--   This is the compatibility of the Eichler–Shimura period map with the Atkin–Lehner involution $w_q$: periods of $w_q f$ along $\gamma$ are periods of $f$ along the conjugate element $\delta$ determined by $\delta \, W.\mathrm{mat} = W.\mathrm{mat}\, \gamma$. It is used in the proof that a Hecke word acts trivially on periods, [`CuspForm.heckeWordHom_eq_zero_of_forall_newLattice`](thm.html#CuspForm.heckeWordHom_eq_zero_of_forall_newLattice).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_periodMap_atkinLehnerLin_apply.lean

import Definitions.Def_ModularCurve_PeriodMapBundled
import Definitions.Def_CuspForm_AtkinLehnerOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CongruenceSubgroup
open scoped MatrixGroups

theorem ModularCurve.periodMap_atkinLehnerLin_apply {M q : ℕ} [NeZero M]
    (W : ModularForm.AtkinLehnerDatum M q) (f : CuspForm (Gamma0 M) 2) (γ δ : Gamma0 M)
    (h : ((δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * W.mat
      = W.mat * ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) :
    ModularCurve.periodMap M (CuspForm.atkinLehnerLin W 2 f) γ = ModularCurve.periodMap M f δ := by sorry
