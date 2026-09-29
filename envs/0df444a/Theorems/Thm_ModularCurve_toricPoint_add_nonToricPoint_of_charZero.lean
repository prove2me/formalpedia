-- Prove2me | Theorems.Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero
-- name    : ModularCurve.toricPoint_add_nonToricPoint_of_charZero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/b0e4c8ab-ba29-5f6a-987c-accbc19a1009
-- title:
--   Additivity of the Tate parametrisation at parameters c q^j
-- statement:
--   Let $F$ be a field of characteristic zero and $M$ a nonzero natural number, and work over the Laurent series field $\mathrm{LaurentSeries}\,F$ with the Weierstrass curve `tateBase F M`, i.e. the Tate curve `tatePowerSeries` over $\mathbb{Z}$ pushed into Laurent series over $F$ and then transported along `qExpand F M`, the ring endomorphism of Laurent series multiplying all exponents by $M$ (so the Tate curve of parameter $q^M$). Two families of affine pairs occur: `toricPoint F M c`, given by the explicit coefficient formulas with constant terms $c/(1-c)^2$ and $c^2/(1-c)^3$ and higher coefficients the indicated divisor sums in $c^{\pm 1}$; and `nonToricPoint F M c j`, obtained by substituting the family `slotFamily F M c j` into the universal bivariate series `tateUnivX`, `tateUnivY` over $\mathbb{Z}$ (whose coefficients are divisor sums and binomial coefficients) and viewing the resulting power series as Laurent series. The theorem asserts the conjunction of three statements. First: for all $c,d\in F^\times$ and all $j$ with $(c:F)\neq 1$ and $0<j<M$, the pairs `toricPoint F M c`, `nonToricPoint F M d j` and `nonToricPoint F M (c*d) j` are nonsingular points of the affine curve, and in the group of affine points the sum of the first two equals the third. Second: for all $c,d\in F^\times$ and $i,j$ with $0<i$, $0<j$ and $i+j<M$, the pairs `nonToricPoint F M c i`, `nonToricPoint F M d j` and `nonToricPoint F M (c*d) (i+j)` are nonsingular and the sum of the first two is the third. Third: for all $c\in F^\times$ and $j$ with $0<j<M$, the pairs `nonToricPoint F M c j` and `nonToricPoint F M c⁻¹ (M-j)` are nonsingular and their sum is the point at infinity.
--
--   This is Tate's theorem that the $q$-expansion parametrisation $u\mapsto (X(u,Q),Y(u,Q))$ of the Tate curve of parameter $Q=q^M$ is a group homomorphism, restricted to the parameters $c\,q^j$ with $c$ a constant and $0\le j<M$, and formulated for the formal Tate curve over $F((q))$ in characteristic zero. It supplies the group law on Tate points that is used in the full-level modular curve computations, in particular in the statements about variable changes on `tateBase`, cusp data and level automorphisms acting on these points.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toricPoint_add_nonToricPoint_of_charZero.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve WeierstrassCurve WeierstrassCurve.Affine

universe u in

theorem ModularCurve.toricPoint_add_nonToricPoint_of_charZero
    (F : Type u) [Field F] [CharZero F] [DecidableEq (LaurentSeries F)] (M : ℕ) [NeZero M] :
    (∀ (c d : Fˣ) (j : ℕ), (c : F) ≠ 1 → 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2),
        (Point.some (toricPoint F M (c : F)).1 (toricPoint F M (c : F)).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) j).1 (nonToricPoint F M (c * d) j).2 hcd) ∧
    (∀ (c d : Fˣ) (i j : ℕ), 0 < i → 0 < j → i + j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c i).1 (nonToricPoint F M c i).2)
        (hd : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M d j).1 (nonToricPoint F M d j).2)
        (hcd : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2),
        (Point.some (nonToricPoint F M c i).1 (nonToricPoint F M c i).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M d j).1 (nonToricPoint F M d j).2 hd
          = Point.some (nonToricPoint F M (c * d) (i + j)).1 (nonToricPoint F M (c * d) (i + j)).2
              hcd) ∧
    (∀ (c : Fˣ) (j : ℕ), 0 < j → j < M →
      ∃ (hc : (tateBase F M).toAffine.Nonsingular (nonToricPoint F M c j).1 (nonToricPoint F M c j).2)
        (hc' : (tateBase F M).toAffine.Nonsingular
          (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2),
        (Point.some (nonToricPoint F M c j).1 (nonToricPoint F M c j).2 hc :
            (tateBase F M).toAffine.Point)
          + Point.some (nonToricPoint F M c⁻¹ (M - j)).1 (nonToricPoint F M c⁻¹ (M - j)).2 hc'
          = 0) := by sorry
