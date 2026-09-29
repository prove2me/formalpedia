-- Prove2me | Theorems.Thm_ModularCurve_hecke_smul_mem_jZeroToricTorsion
-- name    : ModularCurve.hecke_smul_mem_jZeroToricTorsion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/0c1c7d7f-392e-5224-a9b6-f01743f349df
-- title:
--   Hecke stability of the toric m-torsion of J₀(p)
-- statement:
--   Let $p$ be a prime, let $A$ be a valuation subring of $\overline{\mathbb Q}$, and let $m$ be a natural number. Work in $J_0(p) :=$ `JZero p`, the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the function field `modularFunctionFieldBar p`, the base change to $\overline{\mathbb Q}$ of the full modular function field of level $p$, equipped with the $\mathbb T$-module structure `heckeModuleBar p` for $\mathbb T :=$ `HeckeAlg` $= \mathrm{MvPolynomial}\,\mathrm{Nat.Primes}\,\mathbb Z$ (the polynomial ring on one variable per rational prime, acting by evaluating the variables at the Hecke operators `heckeOperatorBar p` when these commute, and by the degenerate evaluation sending every variable to $0$ otherwise). Let `jZeroToricTorsion p A m` be the subgroup $J_0(p)[m] \cap n\cdot J_0(p)^{I_A}$, that is, the intersection of the $\mathbb Z$-torsion submodule killed by $m$ with the image of the subgroup of points fixed by every element of the inertia subgroup of $A$ over $\mathbb Q$ under multiplication by $n = (p-1)/\gcd(p-1,12)$ (`eisensteinNumerator p`). The assertion is: for every $h \in \mathbb T$ and every $x$ in this subgroup, $h\cdot x$ again lies in it. No hypothesis relating $A$ to $p$, and no positivity hypothesis on $m$, is required.
--
--   This is the statement that the toric $m$-torsion of $J_0(p)$ at a place of $\overline{\mathbb Q}$ is a module over the Hecke ring, the two ingredients being that $m$-torsion and multiplication by the Eisenstein numerator are $\mathbb T$-equivariant and that the Hecke action commutes with the Galois action. It is used in the counting estimate [`ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth`](thm.html#ModularCurve.natCard_jZeroToricTorsion_inf_torsionBySet_pow_linearGrowth), where the toric torsion is cut further by powers of an Eisenstein-type ideal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hecke_smul_mem_jZeroToricTorsion.lean

import Definitions.Def_ModularCurve_JZeroToricTorsion
import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.hecke_smul_mem_jZeroToricTorsion
    (p : ℕ) [Fact p.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (m : ℕ)
    (h : HeckeAlg) {x : JZero p} (hx : x ∈ jZeroToricTorsion p A m) :
    (letI := heckeModuleBar p; h • x) ∈ jZeroToricTorsion p A m := by sorry
