-- Prove2me | Theorems.Thm_ModularCurve_heckeTorsion_eisensteinMaximalIdeal_pow_eq_bot_of_not_dvd_eisensteinNumerator
-- name    : ModularCurve.heckeTorsion_eisensteinMaximalIdeal_pow_eq_bot_of_not_dvd_eisensteinNumerator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/77123ea6-4dd1-5b8e-a254-7293a816c5d1
-- title:
--   Vanishing of mathfrak P_q^M-torsion in J₀(p) when q ∤ n(p)
-- statement:
--   Let $p$ and $q$ be primes and let $M$ be a natural number. Write $\mathbb T =$ `HeckeAlg` for the polynomial ring $\mathbb Z[X_\ell]$ over the indeterminates indexed by the primes, and let `JZero p` be the degree-zero divisor class group $\mathrm{Pic}^0$ of the level-$p$ modular function field base-changed to $\overline{\mathbb Q}$, i.e. the quotient of degree-zero divisors by principal ones for `modularFunctionFieldBar p` inside the Laurent series over $\overline{\mathbb Q}$. The ideal `eisensteinMaximalIdeal p q` is the preimage, under the $\mathbb Z$-algebra map $\mathbb T \to \mathbb Z$ evaluating the indeterminates at the Eisenstein system of level $p$, of the ideal $(q) \subseteq \mathbb Z$. The $\mathbb T$-module structure on `JZero p` is `heckeModuleBar p`: the action through `heckeEvalBar` by the Hecke operators on $\mathrm{Pic}^0$ if these operators commute, and otherwise the degenerate action obtained by sending every indeterminate to $0$. Assume $q$ does not divide `eisensteinNumerator p` $= (p-1)/\gcd(p-1,12)$. Then the submodule of elements of `JZero p` annihilated by every element of $(\,$`eisensteinMaximalIdeal p q`$)^M$, namely `Submodule.torsionBySet`, is trivial.
--
--   This is the statement that the Eisenstein-primary torsion of the Jacobian of $X_0(p)$ over $\overline{\mathbb Q}$ is supported only at primes dividing the numerator $n(p)$ of $(p-1)/12$, in the form of Mazur's analysis of the Eisenstein ideal. It feeds the growth estimate [`ModularCurve.jZeroNeronTorsionSheaf_growth_v5`](thm.html#ModularCurve.jZeroNeronTorsionSheaf_growth_v5).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeTorsion_eisensteinMaximalIdeal_pow_eq_bot_of_not_dvd_eisensteinNumerator.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.heckeTorsion_eisensteinMaximalIdeal_pow_eq_bot_of_not_dvd_eisensteinNumerator
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hq : ¬ q ∣ eisensteinNumerator p) (M : ℕ) :
    letI := heckeModuleBar p
    heckeTorsion (JZero p) ((eisensteinMaximalIdeal p q) ^ M) = ⊥ := by sorry
