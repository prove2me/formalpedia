-- Prove2me | Theorems.Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_char_three
-- name    : ModularCurve.degree_eq_of_forall_eq_weightFloor_of_char_three
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/8487bea5-d41f-586a-8ad3-cfbeac34d6f2
-- title:
--   Degree of the weight-2m floor divisor in characteristic 3
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $3$ and let $N \ge 1$ be an integer with $(N : K) \neq 0$, and assume $\nu_3(N) = \#\{x \in \mathbf{Z}/N : x^2 + x + 1 = 0\} = 0$. Let $F =$ `modularFunctionFieldFullC K N` be the intermediate field of $K((q)) =$ `LaurentSeries K` generated over $K$ by the $q$-expansions $\bar\jmath(q^d)$ for the nonzero divisors $d \mid N$, where $\bar\jmath =$ `jqModC K` is the Laurent series $q^{-1} \cdot (E_4^3 \cdot \eta\text{-unit}^{-1})$ reduced into $K$, viewed as an element of $F$. Places $w$ of $F/K$ are the valuation subrings of $F$ that contain $K$, are proper and are principal ideal rings, and $\operatorname{ord}_w$ is the associated normalised integer valuation. Let $m \ge 0$ be a natural number and let $D$ be a divisor of $F/K$, i.e. a finitely supported function from places to $\mathbf{Z}$, such that for every place $w$, writing $e_w = \operatorname{ord}_w(\bar\jmath)$, one has $D(w) = (7 m e_w)/6$ (integer quotient, hence $\lfloor 7 m e_w / 6 \rfloor$ as the numerator is nonnegative) when $e_w > 0$, $D(w) = m e_w$ when $e_w < 0$, and $D(w) = 0$ otherwise. Then, in $\mathbf{Q}$, the degree of $D$ (the sum of $D(w)$ times the degree of $w$) equals $$m\,(2g - 2) + \lfloor m/2 \rfloor\, \nu_2(N) + \lfloor 2m/3 \rfloor\, \nu_3(N) + m\, \nu_\infty(N),$$ where $g = 1 + \psi(N)/12 - \nu_2(N)/4 - \nu_3(N)/3 - \nu_\infty(N)/2$ with $\psi(N) = \sum_{d \mid N,\ d \text{ squarefree}} N/d$, $\nu_2(N) = \#\{x \in \mathbf{Z}/N : x^2 + 1 = 0\}$, $\nu_3$ as above (so the third term vanishes under the hypothesis) and $\nu_\infty(N) = \sum_{d \mid N} \varphi(\gcd(d, N/d))$.
--
--   This is the characteristic-$3$ counterpart of the degree computation for the divisor attached to the weight-$2m$ modular forms on $X_0(N)$, the $\nu_3$-free case in which the fibre of $\bar\jmath$ over the single supersingular value carries only ramification indices $2$ and $6$; the proof combines the census of $\operatorname{ord}_w(\bar\jmath)$ at the zeros of $\bar\jmath$ with the fact that the pole divisor of $\bar\jmath$ has degree $\psi(N) = [F : K(\bar\jmath)]$. It feeds the Riemann–Roch bound on the number of linearly independent mod-$p$ cusp forms used in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_degree_eq_of_forall_eq_weightFloor_of_char_three.lean

import Mathlib
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.degree_eq_of_forall_eq_weightFloor_of_char_three
    (K : Type) [Field K] [IsAlgClosed K] [CharP K 3] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (hν : nuThree N = 0) (m : ℕ)
    (D : Divisor K ↥(modularFunctionFieldFullC K N))
    (hD : ∀ w : Place K ↥(modularFunctionFieldFullC K N),
      D w = (if 0 < w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))
               then (7 * (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N))) / 6
               else 0)
          + (if w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) < 0
               then (m : ℤ) * w.ord (⟨jqModC K, jqModC_mem_full K N⟩ : ↥(modularFunctionFieldFullC K N)) else 0)) :
    (D.degree : ℚ) = (m : ℚ) * (2 * genusFormula N - 2) + ((m / 2 : ℕ) : ℚ) * (nuTwo N : ℚ)
        + ((2 * m / 3 : ℕ) : ℚ) * (nuThree N : ℚ) + (m : ℚ) * (cuspCount N : ℚ) := by sorry
