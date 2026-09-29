-- Prove2me | Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula
-- name    : ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/db11f309-8d92-554c-9c92-76fbdde0c34f
-- title:
--   Genus of the modular function field equals 1+ψ/12-ν₂/4-ν₃/3-c_∞/2
-- statement:
--   Let $N$ be a nonzero natural number and let $F_N$ denote the field [`ModularCurve.modularFunctionFieldBar N`](def/ModularCurve_ArithmeticGalois.html#L111), that is the intermediate field of $\overline{\mathbb Q}((q))$ generated over $K = \overline{\mathbb Q} =$ `AlgebraicClosure ℚ` by the image, under the coefficient embedding of $\mathbb Q((q))$ into $\overline{\mathbb Q}((q))$, of the field `modularFunctionFieldFull N` obtained by adjoining to $\mathbb Q$ inside $\mathbb Q((q))$ the family `divisorExpansions N`. Assume `HasCanonicalDivisor` for the extension $K \subseteq F_N$: for every nonzero Kähler differential $\omega \in \Omega_{F_N/K}$ the function $v \mapsto v.\mathrm{ordDifferential}\,\omega$ on the places of $F_N$ over $K$ is finitely supported, hence is a divisor. Then the natural number [`AlgebraicCurve.genus`](def/AlgebraicCurve_CanonicalDivisor.html#L33) of $K \subseteq F_N$ — computed as $(\deg D + 2).\mathrm{toNat}$ divided by $2$ in $\mathbb N$, for $D$ the canonical divisor attached to some nonzero differential, and $0$ if none exists — equals, after casting to $\mathbb Q$, the rational number $$1 + \frac{\psi(N)}{12} - \frac{\nu_2(N)}{4} - \frac{\nu_3(N)}{3} - \frac{c_\infty(N)}{2},$$ where $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, $\nu_2(N) = \#\{x \in \mathbb Z/N : x^2+1 = 0\}$, $\nu_3(N) = \#\{x \in \mathbb Z/N : x^2+x+1 = 0\}$ and $c_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$. In particular this rational number is a nonnegative integer.
--
--   This is the classical genus formula for the modular curve $X_0(N)$, here expressed through the divisor-theoretic genus of its function field over $\overline{\mathbb Q}$, with $\psi(N) = [\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]$, $\nu_2$ and $\nu_3$ counting elliptic points of orders $2$ and $3$, and $c_\infty$ the number of cusps. It feeds the comparison between the genus and the dimension of the space of weight-two cusp forms for $\Gamma_0(N)$, used in [`CuspForm.dimFormula_le_finrank_gamma0`](thm.html#CuspForm.dimFormula_le_finrank_gamma0) and [`CuspForm.genusFormula_le_finrank_gamma0_weight_two`](thm.html#CuspForm.genusFormula_le_finrank_gamma0_weight_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula (N : ℕ) [NeZero N]
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar N))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar N) : ℚ)
      = ModularCurve.genusFormula N := by sorry
