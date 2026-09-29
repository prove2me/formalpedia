-- Prove2me | Theorems.Thm_ModularCurve_JZero_offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot
-- name    : ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/db17ded5-2a8e-51b1-a751-70cc58d5f5e8
-- title:
--   Off-cusp mass is at most the genus when L(D^∘-∞)=0
-- statement:
--   Fix $N\ge 1$ and work with the field $F_N=\,$`modularFunctionFieldBar N`, the intermediate field of the Laurent series field over $\overline{\mathbb Q}$ obtained by adjoining to $\overline{\mathbb Q}$ the coefficientwise images of the field $\mathbb Q(\text{divisorExpansions } N)$; its places are the valuation subrings of $F_N$ containing $\overline{\mathbb Q}$, proper and with principal ideals, and a divisor is a finitely supported $\mathbb Z$-valued function on them. Let $D$ be such a divisor and write $D^{\circ}=D.\mathrm{erase}\,(\text{cuspInftyBar }N)$ for the divisor agreeing with $D$ away from the $q$-adic place at infinity and vanishing there. The hypothesis is that the Riemann–Roch space of $D^{\circ}-1\cdot(\text{cuspInftyBar }N)$, namely the $\overline{\mathbb Q}$-subspace of $f\in F_N$ with $v(f)\le \exp\bigl((D^{\circ}-1\cdot\infty)(v)\bigr)$ for every place $v$, is the zero submodule. The conclusion is that $\mathrm{offBaseMass}\,N\,D$, the sum of the values of $D^{\circ}$, is at most the integer $\mathrm{genusFF}(\overline{\mathbb Q},F_N)=\dim_{\overline{\mathbb Q}} H^1(0)$, the repartition-theoretic genus of $F_N$.
--
--   This is the elementary Riemann-inequality bound saying that a divisor whose off-cusp part, after subtracting the cusp, has no nonzero section carries off-cusp mass at most the genus; it is the arithmetic input behind representing classes in $J_0(N)$ by at most $g$ points away from the cusp. It is used in [`ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm`](thm.html#ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve
open AlgebraicCurve

theorem ModularCurve.JZero.offBaseMass_le_genusFF_of_riemannRochSpace_eq_bot (N : ℕ) [NeZero N]
    {D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)}
    (h : riemannRochSpace (D.erase (cuspInftyBar N) - Finsupp.single (cuspInftyBar N) (1 : ℤ)) = ⊥) :
    offBaseMass N D ≤ (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℤ) := by sorry
