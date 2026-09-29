-- Prove2me | Theorems.Thm_ModularCurve_mem_riemannRochSpace_of_isModPFormFn
-- name    : ModularCurve.mem_riemannRochSpace_of_isModPFormFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/8fdaee14-2a3a-57f2-8bc0-862295f43d59
-- title:
--   Integral weight-2m holomorphy gives membership in L(D)
-- statement:
--   Let $K$ be a field in which $1728 \neq 0$, let $N \geq 1$ and let $m$ be a natural number. Write $F =$ `modularFunctionFieldFullC K N` for the intermediate field of the Laurent series field $K((q))$ generated over $K$ by the series `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$, and write $\bar j \in F$ for the element `jqModC K`, the Laurent series $q^{-1}$ times the image in $K$ of the integral power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`. Let $D$ be a divisor of $F/K$, i.e. a finitely supported integer-valued function on the places of $F/K$ (valuation subrings of $F$ containing $K$, proper, and principal ideal rings), and assume that at every place $w$ its value is $$D(w) = \bigl[\operatorname{ord}_w \bar j > 0\bigr]\cdot \tfrac{2m\,\operatorname{ord}_w \bar j}{3} + \bigl[\operatorname{ord}_w(\bar j - 1728) > 0\bigr]\cdot\tfrac{m\,\operatorname{ord}_w(\bar j - 1728)}{2} + \bigl[\operatorname{ord}_w \bar j < 0\bigr]\cdot m\,\operatorname{ord}_w \bar j,$$ the two quotients being integer division (so, the numerators being positive, the floors of $2m\,\operatorname{ord}_w\bar j/3$ and of $m\,\operatorname{ord}_w(\bar j-1728)/2$), and $\operatorname{ord}_w$ denoting $-\log$ of the adic valuation attached to $w$. Let $G \in F$ satisfy `IsModPFormFn K m`, that is: $G^6\,\bar j^{4m}(\bar j - 1728)^{3m}$ is integral over $K[\bar j]$ and $G^2\,\bar j^{m}(\bar j - 1728)^{m}$ is integral over $K[\bar j^{-1}]$. Then $G$ lies in the Riemann–Roch space $L(D)$, i.e. at every place $w$ the adic valuation of $G$ is at most $\exp(D(w))$, equivalently $\operatorname{ord}_w G \geq -D(w)$ for all $w$.
--
--   This is the forward half of the dictionary between the integrality form of holomorphy of weight $2m$ for an element of the full level-$N$ modular function field and membership in the Riemann–Roch space of the associated weight-$2m$ floor divisor, the divisor allowing poles of order $\lfloor 2me/3\rfloor$ and $\lfloor me/2\rfloor$ at the zeros of $\bar j$ and of $\bar j - 1728$ of multiplicity $e$ and requiring zeros at the poles of $\bar j$. It feeds the Riemann–Roch bound on the number of linearly independent such functions ([`ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent`](thm.html#ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent)) and the congruence statement [`ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero`](thm.html#ModularCurve.SSHeckeV2.mem_modPMod_sub_of_resQFun_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_riemannRochSpace_of_isModPFormFn.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.mem_riemannRochSpace_of_isModPFormFn
    (K : Type) [Field K] (h1728 : (1728 : K) ≠ 0) (N : ℕ) [NeZero N] (m : ℕ)
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0))
    (G : ↥(modularFunctionFieldFullC K N)) (hG : IsModPFormFn K m (G : LaurentSeries K)) :
    G ∈ riemannRochSpace D := by sorry
