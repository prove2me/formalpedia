-- Prove2me | Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
-- name    : NumberField.TateGlobal.continuous_ideleNorm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/066acdb9-589e-58c3-8f28-5cec828cd6bd
-- title:
--   Continuity of the idelic norm on A_F^×
-- statement:
--   Let $F$ be a field which is a number field, with ring of integers $\mathcal O_F$ and adele ring $\mathbb A_F =$ `AdeleRing (𝓞 F) F`. For a unit $x$ of $\mathbb A_F$, the quantity `ideleNorm F x` is defined to be the real number obtained from the value at $x$ of the Haar character `distribHaarChar (AdeleRing (𝓞 F) F)`, a non-negative real, by the coercion $\mathbb R_{\ge 0} \to \mathbb R$; concretely, it is the factor by which the scaling action of the idele $x$ multiplies an additive Haar measure on $\mathbb A_F$. The theorem asserts that the resulting function $\mathbb A_F^\times \to \mathbb R$, $x \mapsto$ `ideleNorm F x`, is continuous, the source carrying the topology of the unit group of the topological ring $\mathbb A_F$ (so that both $x \mapsto x$ and $x \mapsto x^{-1}$ are continuous in it) and the target the usual topology on $\mathbb R$. No further hypotheses are imposed, and no positivity or multiplicativity assertion is part of the conclusion.
--
--   This is the continuity half of the classical statement that the module, or idelic norm, is a continuous homomorphism from the idele group of a number field to the positive reals; multiplicativity is immediate from the definition of the Haar character, whereas continuity reflects the fact that the norm is computed place by place and is trivial on the open subgroups of ideles that are units outside a finite set of places. It underlies the analytic work on adelic zeta integrals and automorphic forms built on the idelic norm, and is used widely there, for example in the estimates for class sums and in the Rankin–Selberg integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_continuous_ideleNorm.lean

import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem NumberField.TateGlobal.continuous_ideleNorm (F : Type) [Field F] [NumberField F] :
    Continuous (NumberField.TateGlobal.ideleNorm F) := by sorry
