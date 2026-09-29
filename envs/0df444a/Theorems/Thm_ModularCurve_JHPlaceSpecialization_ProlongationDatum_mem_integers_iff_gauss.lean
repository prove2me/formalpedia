-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/10e70a30-f402-574e-bd69-2fccb9304e80
-- title:
--   First prolongation equals the Gauss ring of q-expansions
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ but $p^2 \nmid M$ (so $M/p$ is again nonzero), and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing the whole kernel of the reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$, i.e. $u \in H$ whenever `ZMod.unitsMap` sends $u$ to $1$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$, meaning that $p$ belongs to the nonunits of $A$, and assume its residue field $\kappa$ is algebraically closed of characteristic $p$. Write $F_M$ for `xHFunctionFieldBar M H`, the compositum of $\overline{\mathbb{Q}}$ with the level-$M$ function field inside $\overline{\mathbb{Q}}((q))$. Let $\theta$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$, let `Psp` be a place specialisation of type `JHPlaceSpecialization p M H hpM A`, and let `Rpd` be any prolongation datum over `Psp` and $\theta$, so in particular `Rpd.R₁` is a regular prolongation of $A$ to $F_M$ with residue field $\overline{F}$, whose integers contain each $A$-integral $q$-expansion with residue the reduced $q$-expansion. Then, for every $f \in F_M$, $f$ lies in the valuation subring `Rpd.R₁.integers` if and only if there exist Laurent series $x, y$ with coefficients in $A$ such that the coefficientwise reduction of $y$ to $\kappa((q))$ is nonzero and $f \cdot y = x$ as Laurent series over $\overline{\mathbb{Q}}$.
--
--   This identifies the first prolongation in any prolongation datum at a prime $p$ exactly dividing the level with the Gauss ring of $q$-expansions: the ring of quotients $x/y$ of $A$-integral Laurent series whose denominator has nonvanishing reduction. It is used by the consumers of the place-specialisation package, where intrinsic properties of `Rpd.R₁` — residues of $q$-expansions, orders at places, and compatibility with Frobenius and with the Hecke action — must be read off from $q$-expansions rather than from the abstract structure fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_mem_integers_iff_gauss.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RegularProlongation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.mem_integers_iff_gauss
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ) :
    ∀ f : ↥(xHFunctionFieldBar M H), f ∈ Rpd.R₁.integers ↔
      ∃ x y : LaurentSeries ↥A, coeffMap (IsLocalRing.residue ↥A) y ≠ 0 ∧
        ((f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x := by sorry
