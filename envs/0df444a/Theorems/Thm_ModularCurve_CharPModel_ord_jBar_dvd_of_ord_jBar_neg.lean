-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg
-- name    : ModularCurve.CharPModel.ord_jBar_dvd_of_ord_jBar_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/421c2225-b852-54b0-bc61-5f453fc1de1b
-- title:
--   Poles of ̄ j on X₀(N) have order dividing N
-- statement:
--   Let $N$ be a natural number that is nonzero. Write $\bar F_N$ for the intermediate field `modularFunctionFieldBar N` of the Laurent series field $\overline{\mathbb{Q}}((q))$ over $\overline{\mathbb{Q}}$, namely the subfield generated over $\overline{\mathbb{Q}}$ by the coefficientwise images, under the map $\mathbb{Q}((q)) \to \overline{\mathbb{Q}}((q))$ induced by $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}$, of the field `modularFunctionFieldFull N`, which in turn is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the expansions `divisorExpansions N`. Let $b$ be a place of $\bar F_N$ over $\overline{\mathbb{Q}}$ in the sense of the project's structure [`AlgebraicCurve.Place`](def/AlgebraicCurve_DivisorClassGroup.html#L22): a valuation subring of $\bar F_N$ containing the image of $\overline{\mathbb{Q}}$, distinct from the whole field, and a principal ideal ring. Let `jBar N` be the element of $\bar F_N$ given by the coefficientwise image of the $q$-expansion of $j$, and let $b.\mathrm{ord}$ denote minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation. Assuming $\mathrm{ord}_b(\bar j) < 0$, the conclusion is that $\mathrm{ord}_b(\bar j)$ divides $N$ in $\mathbb{Z}$.
--
--   The places of $\bar F_N$ at which $\bar j$ has a pole are the cusps of $X_0(N)$ over $\overline{\mathbb{Q}}$, and $-\mathrm{ord}_b(\bar j)$ is the width of the cusp $b$; the assertion is the classical fact that cusp widths of $\Gamma_0(N)$ divide $N$ (a divisibility, not an equality: the cusp of denominator $2$ at level $8$ has width $2$). It is used in the construction of divisors built from modular units on the characteristic-$p$ fibre models, via [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_ord_jBar_dvd_of_ord_jBar_neg.lean

import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.CharPModel.ord_jBar_dvd_of_ord_jBar_neg (N : ℕ) [NeZero N]
    (b : AlgebraicCurve.Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hb : b.ord (jBar N) < 0) : b.ord (jBar N) ∣ (N : ℤ) := by sorry
