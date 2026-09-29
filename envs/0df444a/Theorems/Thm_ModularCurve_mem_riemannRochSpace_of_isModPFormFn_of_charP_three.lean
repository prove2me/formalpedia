-- Prove2me | Theorems.Thm_ModularCurve_mem_riemannRochSpace_of_isModPFormFn_of_charP_three
-- name    : ModularCurve.mem_riemannRochSpace_of_isModPFormFn_of_charP_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/94e5cdd5-a957-5aa5-8ee8-4de5f44e04a4
-- title:
--   Holomorphic weight-2m mod 3 forms lie in L(D)
-- statement:
--   Let $N\ge 1$ be an integer not divisible by $3$ and admitting a prime divisor $q$ with $q\equiv 2 \pmod 3$, let $K$ be an algebraically closed field of characteristic $3$, and let $m\ge 0$. Write $F_N =$ `modularFunctionFieldFullC K N` for the intermediate field of $K((q))$ generated over $K$ by the series $\mathrm{qExpand}\,K\,d\,(\bar\jmath)$ for the nonzero divisors $d$ of $N$, where $\bar\jmath =$ `jqModC K` is the $q$-expansion $q^{-1}\cdot(E_4^3\eta^{-24})$ of the $j$-invariant reduced to $K$, viewed as an element of $F_N$. Let $D$ be a finitely supported $\mathbb{Z}$-valued function on the places of $F_N$ over $K$ (each place being a proper valuation subring of $F_N$ containing $K$ whose ring is a principal ideal ring) such that for every such place $w$, with $e = \operatorname{ord}_w\bar\jmath = -\log w(\bar\jmath)$ and $e' = \operatorname{ord}_w(\bar\jmath - 1728)$, one has $D(w) = \lfloor 2me/3\rfloor$ if $e>0$ (and $0$ otherwise), plus $\lfloor me'/2\rfloor$ if $e'>0$ (and $0$ otherwise), plus $me$ if $e<0$ (and $0$ otherwise); since $1728 = 0$ in $K$, the second clause is again a clause about $\operatorname{ord}_w\bar\jmath$. Finally let $G\in F_N$ satisfy `IsModPFormFn K m`, i.e. $G^6\,\bar\jmath^{4m}(\bar\jmath - 1728)^{3m}$ is integral over the $K$-subalgebra $K[\bar\jmath]$ of $K((q))$ and $G^2\,\bar\jmath^{m}(\bar\jmath - 1728)^{m}$ is integral over $K[\bar\jmath^{-1}]$. Then $G$ lies in the Riemann–Roch space of $D$: for every place $w$ of $F_N$ over $K$ one has $w(G)\le \exp(D(w))$, that is $\operatorname{ord}_w G \ge -D(w)$.
--
--   This is the characteristic-$3$ form of the statement that a function holomorphic of weight $2m$ in the integrality sense lies in the Riemann–Roch space of the associated floor divisor, the divisor clause being kept in the same shape as in residue characteristics where $1728\ne 0$. It supplies the Riemann–Roch side of the dimension bound for spaces of mod $3$ modular functions, and is used by [`ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent_of_charP_three`](thm.html#ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent_of_charP_three).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_riemannRochSpace_of_isModPFormFn_of_charP_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.mem_riemannRochSpace_of_isModPFormFn_of_charP_three
    (N : ℕ) [NeZero N] (hpN : ¬ 3 ∣ N) (hε : ∃ q : ℕ, q.Prime ∧ q ∣ N ∧ q % 3 = 2)
    (K : Type) [Field K] [CharP K 3] [IsAlgClosed K] (m : ℕ)
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
