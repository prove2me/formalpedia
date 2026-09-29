-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le
-- name    : ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/518b932e-b9e1-50fe-afab-346440b7c400
-- title:
--   Non-integral j at w forces a pole at sp(w)
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime, $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and divisibility data $p \mid M$ together with $p^2 \nmid M$ (and $M/p \neq 0$). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that the image of $p$ lies in the non-units of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed, and let $\mathrm{Psp}$ be a specialization packet `JHPlaceSpecialization p M H hpM A`, whose component `sp` carries places of $F' =$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` — the base change to $\overline{\mathbb{Q}}$, inside Laurent series over $\overline{\mathbb{Q}}$, of the function field of level $M/p$ for the image of $H$ under reduction — to places of $\bar F' =$ `JHNeronObjectAtP.Fbar p M H hpM κ` over $\kappa$, subject to the divisor-, Picard-, inertia- and Frobenius-compatibilities recorded in that structure. The assertion is: for all $x \in F'$ and $\bar x \in \bar F'$ whose Laurent expansions are the $j$-series $q^{-1}\bigl(1 + \cdots\bigr)$, namely `jqModC` over $\overline{\mathbb{Q}}$ and over $\kappa$ respectively, and for every place $w$ of $F'$ over $\overline{\mathbb{Q}}$, if $\mathrm{ord}_w\bigl(x - a\bigr) \le 0$ for every $a \in A$ (images under the structure map), then $\mathrm{ord}_{\mathrm{Psp}.\mathrm{sp}(w)}(\bar x) < 0$.
--
--   The statement says that the specialization of places carries the Tate region of $X_{H'}(M/p)$ into the cusps: a place at which $j$ attains no $A$-integral value is sent to a pole of the reduced $j$-invariant. It is used in the prolongation-datum constructions for `JHPlaceSpecialization`, where cusps and affine places must be separated after specialization.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ord_sp_neg_of_forall_ord_sub_algebraMap_le.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ord_sp_neg_of_forall_ord_sub_algebraMap_le
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A) :
    ∀ (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
      ∀ (w : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
        (∀ a : ↥A, w.ord (x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)) ≤ 0) →
        (Psp.sp w).ord xb < 0 := by sorry
