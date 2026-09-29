-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/47738749-e695-52d3-808c-db4bef1858b3
-- title:
--   Incomparability of the two prolongations of a Γ_H datum
-- statement:
--   Fix natural numbers $p$, $M$ with $p$ prime, a subgroup $H \le (\mathbb{Z}/M)^\times$, and assume $p \mid M$ but $p^2 \nmid M$, together with the hypothesis that every unit of $\mathbb{Z}/M$ reducing to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$ (so $H$ is the full preimage of its image). Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M$ for the intermediate field $\overline{\mathbb{Q}} \cdot F(\Gamma_H(M))$ inside $\overline{\mathbb{Q}}((q))$, and $F_{M/p}$ for the corresponding field at level $M/p$ with the subgroup `infSubgroup`, the image of $H$ under reduction. Given a $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M$, an integral $\overline{\mathbb{Q}}$-algebra map $\alpha : F_{M/p} \to F_M$ preserving underlying Laurent series, a place-specialisation datum `JHPlaceSpecialization` for $(p,M,H,A)$, and a prolongation datum relative to $\theta$, consisting of two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residue field $\bar F$, where membership in $R_2$'s valuation ring means $\theta f$ lies in $R_1$'s and $R_2$'s residue of $f$ is $R_1$'s residue of $\theta f$: assume that for every $v \in F_{M/p}$ with $\alpha v$ in both valuation rings, the $R_2$-residue of $\alpha v$ is the $q$-expansion Frobenius `qExpFrobeniusModL` at $p$ applied to the $R_1$-residue, and assume there exists $x \in F_{M/p}$ whose Laurent series is the $q$-expansion `jqModC` of $j$. Then the two valuation subrings are incomparable: neither $R_1$'s integers are contained in $R_2$'s, nor conversely.
--
--   The statement records that the two Gauss-type prolongations attached to a prolongation datum at a prime exactly dividing the level are incomparable valuation rings of $F_M$, reflecting the two components of the reduction of $X_H(M)$ at $p$ interchanged by Frobenius. It is the incomparability (weak approximation) input to [`ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL`](thm.html#ModularCurve.XHDRModelAtP.integers_ne_and_forall_valuationSubring_eq_or_eq_of_residue_eq_qExpFrobeniusModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_not_integers_le_integers_and_not_integers_le_integers.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.not_integers_le_integers_and_not_integers_le_integers
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hres₂α : ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩))
    (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hx : ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ)) :
    ¬ Rpd.R₁.integers ≤ Rpd.R₂.integers ∧ ¬ Rpd.R₂.integers ≤ Rpd.R₁.integers := by sorry
