-- Prove2me | Theorems.Thm_ModularCurve_smul_mem_jZeroToricTorsion
-- name    : ModularCurve.smul_mem_jZeroToricTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/e2a51e3f-0437-5293-ae3d-ecdd2cb33cb9
-- title:
--   Hecke stability of the toric m-torsion of J₀(p)
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, a natural number $m$, and an element $t$ of the abstract Hecke algebra `HeckeAlg`, the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$ in indeterminates indexed by the primes. Let $J_0(p)$ denote `JZero p`, the degree-zero divisor class group $\operatorname{Pic}^0$ of the modular function field of level $p$ base-changed to $\overline{\mathbb Q}$, equipped with the `HeckeAlg`-module structure `heckeModuleBar p` (given by the ring homomorphism sending each indeterminate to the corresponding Hecke operator, the Hecke operators being known to commute, and by the trivial specialisation otherwise). The assertion is that the subgroup `jZeroToricTorsion p A m`, namely the intersection of the $m$-torsion $\{x : (m : \mathbb Z) \cdot x = 0\}$ with the image of the group of points fixed by every element of the inertia subgroup of $A$ in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ under multiplication by the Eisenstein numerator $n = (p-1)/\gcd(p-1,12)$, is stable under $t$: if $x$ lies in it, so does $t \cdot x$.
--
--   This is the Hecke-stability of the toric $m$-torsion at a place $A$ of $\overline{\mathbb Q}$, in the form used when Hecke operators are extended to the integral model of $J_0(p)$. It is cited in the construction of integral points through torsion points lying over $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_smul_mem_jZeroToricTorsion.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_JZeroNeronDataPrime
import Definitions.Def_ModularCurve_JZeroNeronData
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.smul_mem_jZeroToricTorsion (p : ℕ) [Fact p.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ) (t : HeckeAlg) {x : JZero p}
    (hx : x ∈ jZeroToricTorsion p A m) :
    (letI := heckeModuleBar p; t • x) ∈ jZeroToricTorsion p A m := by sorry
