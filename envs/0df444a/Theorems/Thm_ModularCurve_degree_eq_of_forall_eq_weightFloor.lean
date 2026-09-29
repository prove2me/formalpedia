-- Prove2me | Theorems.Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor
-- name    : ModularCurve.degree_eq_of_forall_eq_weightFloor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/3bd68245-7e87-5c8e-a5a9-bf2be027afce
-- title:
--   Degree of the weight-2m floor divisor on X₀(N)
-- statement:
--   Let $K$ be an algebraically closed field, let $N \ge 1$ with $6N \neq 0$ in $K$, and let $m$ be a natural number. Let $F$ be `modularFunctionFieldFullC K N`, the subfield of the Laurent series field over $K$ generated over $K$ by the series `qExpand K d (jqModC K)` for the nonzero divisors $d$ of $N$, where `jqModC K` is $q^{-1}$ times the image over $K$ of the power series $E_4^3 \cdot$ `dedekindEtaUnitInv`, i.e. the $q$-expansion of $j$; write $j \in F$ for `jqModC K` itself. Places of $F$ over $K$ are valuation subrings of $F$ containing $\operatorname{im}(K)$, proper, and principal ideal rings, and $\mathrm{ord}_w$ denotes the associated $\mathbb{Z}$-valued order function. Assume that for every place $w$ one has $\mathrm{ord}_w(j) \mid 3$ whenever $\mathrm{ord}_w(j) > 0$, and $\mathrm{ord}_w(j - 1728) \mid 2$ whenever $\mathrm{ord}_w(j-1728) > 0$. Let $D$ be a divisor of $F$ over $K$ (a finitely supported integer-valued function on places) such that for every place $w$,
--   $$D(w) = \big[\mathrm{ord}_w(j) > 0\big]\,\Big\lfloor \tfrac{2m\,\mathrm{ord}_w(j)}{3} \Big\rfloor + \big[\mathrm{ord}_w(j-1728) > 0\big]\,\Big\lfloor \tfrac{m\,\mathrm{ord}_w(j-1728)}{2} \Big\rfloor + \big[\mathrm{ord}_w(j) < 0\big]\, m\,\mathrm{ord}_w(j),$$
--   the quotients being integer division (floors here, the numerators being nonnegative). The conclusion is that the degree of $D$, namely $\sum_w D(w)\deg(w)$, viewed in $\mathbb{Q}$, equals
--   $$m\,(2\,\mathrm{genusFormula}(N) - 2) + \lfloor m/2 \rfloor\,\nu_2(N) + \lfloor 2m/3 \rfloor\,\nu_3(N) + m\,\nu_\infty(N),$$
--   where $\nu_2(N) = \#\{x \in \mathbb{Z}/N : x^2+1 = 0\}$, $\nu_3(N) = \#\{x \in \mathbb{Z}/N : x^2+x+1 = 0\}$, $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$, the floors $\lfloor m/2 \rfloor$ and $\lfloor 2m/3 \rfloor$ are natural-number divisions, and $\mathrm{genusFormula}(N) = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$.
--
--   This is the divisor-degree computation underlying the dimension formula for modular forms of weight $2m$ on $X_0(N)$: the floor divisor attached to the weight-$2m$ automorphy factor, expressed through the order of $j$ and of $j - 1728$ at the places of the modular function field, has the degree predicted by $m(2g-2)$ plus the elliptic and cuspidal correction terms. It feeds the Riemann–Roch half of the dimension count, being cited by [`ModularCurve.ell_eq_dimFormula_of_forall_eq_weightFloor`](thm.html#ModularCurve.ell_eq_dimFormula_of_forall_eq_weightFloor), [`ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one`](thm.html#ModularCurve.degree_weightDivisor_sub_indexPlaces_eq_of_two_mul_eq_add_one) and [`ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent`](thm.html#ModularCurve.card_le_dimFormula_of_isModPFormFn_of_linearIndependent); the inputs are the fibre counts of the $j$-map over $j = 0$ and $j = 1728$ and the degree $[F : K(j)] = \psi(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.degree_eq_of_forall_eq_weightFloor
    (K : Type) [Field K] [IsAlgClosed K] (N : ℕ) [NeZero N] (h6N : ((6 * N : ℕ) : K) ≠ 0) (m : ℕ)
    (hram : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      (0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) →
          w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) ∣ 3) ∧
      (0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) →
          w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728) ∣ 2))
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (2 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 3 else 0)
          + (if 0 < w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)
               then ((m : ℤ) * w.ord ((⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) - algebraMap K _ 1728)) / 2 else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0)) :
    (D.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (m : ℚ) * (cuspCount N : ℚ) := by sorry
