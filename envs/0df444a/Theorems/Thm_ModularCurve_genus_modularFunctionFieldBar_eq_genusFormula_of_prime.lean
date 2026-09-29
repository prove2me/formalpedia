-- Prove2me | Theorems.Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula_of_prime
-- name    : ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/60fae53e-fea0-5ad4-bc46-c121a8986305
-- title:
--   Genus of X₀(p) for an odd prime p
-- statement:
--   Let $p$ be a prime with $p$ odd, and write $K=\overline{\mathbb Q}$ for the algebraic closure of $\mathbb Q$ and $F=$ [`ModularCurve.modularFunctionFieldBar p`](def/ModularCurve_ArithmeticGalois.html#L111) for the subfield of the Laurent series field $K((X))$ generated over $K$ by the image, under the coefficient-wise embedding of $\mathbb Q((X))$ into $K((X))$, of [`ModularCurve.modularFunctionFieldFull p`](def/ModularCurve_X0.html#L305), the subfield of $\mathbb Q((X))$ generated over $\mathbb Q$ by the divisor expansions of level $p$. Assume [`AlgebraicCurve.HasCanonicalDivisor`](def/AlgebraicCurve_CanonicalDivisor.html#L14) for the extension $F/K$, i.e. that for every nonzero Kähler differential $\omega\in\Omega[F/K]$ there is a divisor $D$ — a finitely supported $\mathbb Z$-valued function on the places of $F/K$, a place being a valuation subring of $F$ that contains $K$, is not all of $F$, and is a principal ideal ring — with $D(v)=v.\mathrm{ordDifferential}\,\omega$, the valuation at $v$ of the differential coefficient of $\omega$, for every place $v$. Then the natural number [`AlgebraicCurve.genus`](def/AlgebraicCurve_CanonicalDivisor.html#L33) of $F/K$, namely $(\deg D+2)/2$ computed with the degree $\sum_v D(v)\,\deg v$ of the divisor attached to a chosen nonzero differential, satisfies, as a rational number,
--   $$g=1+\frac{\psi(p)}{12}-\frac{\nu_2(p)}{4}-\frac{\nu_3(p)}{3}-\frac{c(p)}{2},$$
--   where $\psi(N)=\sum_{d\mid N,\ d\ \text{squarefree}}N/d$, $\nu_2(N)=\#\{x\in\mathbb Z/N:x^2+1=0\}$, $\nu_3(N)=\#\{x\in\mathbb Z/N:x^2+x+1=0\}$ and $c(N)=\sum_{d\mid N}\varphi(\gcd(d,N/d))$. For $N=p$ prime one has $\psi(p)=p+1$ and $c(p)=2$, so the right-hand side is $(p+1)/12-\nu_2(p)/4-\nu_3(p)/3$.
--
--   This is the classical genus formula for the modular curve $X_0(N)$, specialised to odd prime level, in the form in which the genus is the canonical-divisor degree of the function field of $X_0(p)$ over $\overline{\mathbb Q}$. It is used in the computations of level-one fibres and in showing that the cuspidal divisor class of $X_0(p)$ is nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_genus_modularFunctionFieldBar_eq_genusFormula_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_GenusNumerics
import Definitions.Def_AlgebraicCurve_CanonicalDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.genus_modularFunctionFieldBar_eq_genusFormula_of_prime (p : ℕ) [Fact p.Prime] (hodd : Odd p)
    [AlgebraicCurve.HasCanonicalDivisor (K := AlgebraicClosure ℚ) (F := ↥(ModularCurve.modularFunctionFieldBar p))] :
    (AlgebraicCurve.genus (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar p) : ℚ)
      = ModularCurve.genusFormula p := by sorry
