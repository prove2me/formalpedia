-- Prove2me | Theorems.Thm_MatMulDS_eq_5_2
-- name    : MatMulDS.eq_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:06:09.683635+00:00
-- url     : https://prove2.me/theorems/359cb9ab-de62-4556-acf0-a1a3027b7aca
-- title:
--   Equation (5.2) with (F1)–(F4) — the five-term identity and its properties
-- statement:
--   Let $\varepsilon$ and the variables $x_1,x_2,p_1,p_2,y_1,y_2,q,z_0,z_{ij}$ be indeterminates. Then
--   $$(x_1+\varepsilon^2p_1)y_1(z_0+\varepsilon^2z_{11})+x_2(y_1-\varepsilon q)(z_0+\varepsilon^2z_{21})+(x_1-\varepsilon p_2)y_2(z_0+\varepsilon^2z_{12})+(x_2+\varepsilon p_2)(y_2+\varepsilon q)(z_0+\varepsilon^2z_{22})+(-x_1-x_2)(y_1+y_2)z_0=\varepsilon^2T_5+O(\varepsilon^3).$$
--   Moreover, the identity has these properties:
--
--   1. (F1) it computes $T_5$ with $h=2$; $z_{ij}$ is computed from the single product $P_{ij}=x_iy_j+O(\varepsilon)$ with coefficient $\varepsilon^2$, and $z_0$ from all five products with coefficient $1$, whose sum is exactly $\varepsilon^2(p_1y_1+p_2q)$;
--   2. (F2) $T_5$ has two blocks, with disjoint left variables and the shared right variable $y_1$;
--   3. (F3) $z_{ij}\mapsto P_{ij}$, $z_0\mapsto P_0$ is a bijective private map;
--   4. (F4) $P_0$ is used only by $z_0$, and the weight of $P_0$ equal to $1$ and of the others equal to $0$ is compatible and strict.
--
--   This identity is the starting point of every identity in the mission.
--
--   Differences from the source:
--   - encoding: the identity holds as a polynomial identity in indeterminates → the first clause holds in every commutative ring with some $G$ such that the remainder is $\varepsilon^3G$; reason: applied to the polynomial ring in the indeterminates this is the source claim
--   - encoding: indices start at $1$; $z_0$, $p_i$, $q$ have their own names → 0-based pairs: $z_0=z_{2,0}$, $p_1=x_{2,0}$, $p_2=x_{2,1}$, $q=y_{1,0}$; reason: the identification of p.28 of the source; same instances
-- source:
--   J. Alman, J. Nogler, V. Vassilevska Williams, Subquadratic Time Matrix Multiplication Data Structures Beyond the Dual Exponent, with Applications, STOC 2027 submission (held file sha256 6c5a1c16…), eq. (5.2), Items (F1)–(F4), p.26 (PDF p.28)

import Mathlib
import Definitions.Def_MatMulDS_fiveTensor

set_option autoImplicit false

open Polynomial

namespace MatMulDS

/-- **Equation (5.2) and Items (F1)–(F4), p.26** (Alman, Nogler, Vassilevska Williams, STOC 2027 submission, held
file sha256 6c5a1c16…). The five-term identity holds, with `h = 2`: the identity (5.2) in every commutative ring, its
form as an approximate bilinear identity for the block tensor `T5`, and the four facts about it.

**Formalization Note** In the universal commutative ring (polynomials in `ε` and the variables), the first clause says
that the left-hand side minus `ε²T5` is divisible by `ε³`. The `0`-based indices are as in `fiveTensor`. -/
theorem eq_5_2 :
    -- (5.2)
    (∀ (R : Type) [CommRing R] (ε x1 x2 p1 p2 y1 y2 q z0 z11 z21 z12 z22 : R), ∃ G : R,
      (x1 + ε ^ 2 * p1) * y1 * (z0 + ε ^ 2 * z11) + x2 * (y1 - ε * q) * (z0 + ε ^ 2 * z21) +
        (x1 - ε * p2) * y2 * (z0 + ε ^ 2 * z12) + (x2 + ε * p2) * (y2 + ε * q) * (z0 + ε ^ 2 * z22) +
        (-x1 - x2) * (y1 + y2) * z0 =
      ε ^ 2 * (x1 * y1 * z11 + x2 * y1 * z21 + x1 * y2 * z12 + x2 * y2 * z22 +
        (p1 * y1 + p2 * q) * z0) + ε ^ 3 * G) ∧
    fiveData.Computes fiveTensor ∧ fiveData.h = 2 ∧
    -- (F1) decoding
    (∀ p, fiveData.C (2, 0) p = 1) ∧
    (∀ (o : Fin 2 × Fin 2) (p : Fin 5),
      fiveData.C ((o.1 : Fin 2).castSucc, o.2) p =
        if p = fivePrivateFn ((o.1 : Fin 2).castSucc, o.2) then X ^ 2 else 0) ∧
    (∀ (o : Fin 2 × Fin 2) (a : Fin 3 × Fin 2) (b : Fin 2 × Fin 2),
      (X : ℚ[X]) ∣ fiveData.U (fivePrivateFn ((o.1 : Fin 2).castSucc, o.2)) a *
          fiveData.V (fivePrivateFn ((o.1 : Fin 2).castSucc, o.2)) b -
        if a = ((o.1 : Fin 2).castSucc, 0) ∧ b = (0, o.2) then 1 else 0) ∧
    fiveData.IsCentralOutput fiveTensor (2, 0) ∧
    -- (F2) two blocks
    fiveTensor.blockOutputs 0 = {(0, 0), (1, 0), (0, 1), (1, 1)} ∧
    fiveTensor.mids 0 = {0} ∧
    fiveTensor.blockOutputs 1 = {(2, 0)} ∧
    fiveTensor.mids 1 = {0, 1} ∧
    Disjoint (fiveTensor.rows 0 ×ˢ fiveTensor.mids 0) (fiveTensor.rows 1 ×ˢ fiveTensor.mids 1) ∧
    ((0, 0) : Fin 2 × Fin 2) ∈ fiveTensor.mids 0 ×ˢ fiveTensor.cols 0 ∧
    ((0, 0) : Fin 2 × Fin 2) ∈ fiveTensor.mids 1 ×ˢ fiveTensor.cols 1 ∧
    -- (F3) private products
    fiveData.IsPrivateMap fiveTensor fivePrivate ∧ IsBijective fiveTensor (Fin 5) ∧
    -- (F4) a weight
    (∀ o : fiveTensor.Out, (4 : Fin 5) ∈ fiveData.Prel o.1 → o.1 = (2, 0)) ∧
    fiveData.IsCompatible fiveTensor fivePrivate fiveWeight ∧
    fiveData.IsStrict fiveTensor fivePrivate fiveWeight := by sorry

end MatMulDS
