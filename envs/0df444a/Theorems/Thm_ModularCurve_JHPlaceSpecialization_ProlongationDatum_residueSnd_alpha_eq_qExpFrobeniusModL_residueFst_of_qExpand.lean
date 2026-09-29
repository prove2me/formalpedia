-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
-- name    : ModularCurve.JHPlaceSpecialization.ProlongationDatum.residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/007724b5-1f39-5125-8655-21b1ccc430f7
-- title:
--   Second residue of a lower-level function is Frobenius of first
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image under reduction $(\mathbb{Z}/M)^\times \to (\mathbb{Z}/(M/p))^\times$ is trivial. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the content of `LiesOverPrime`), whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Let $\alpha$ be a $\overline{\mathbb{Q}}$-algebra map from $F_{M/p} :=$ `xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)` to $F_M :=$ `xHFunctionFieldBar M H` which is the identity on the underlying Laurent series (the degeneracy embedding, read on $q$-expansions), and let $\theta_0$ be a $\overline{\mathbb{Q}}$-algebra automorphism of $F_M$ obeying the $q$-expansion law: whenever $f \in F_M$ and $u \in F_{M/p}$ have the same Laurent series, the series of $\theta_0 f$ is `qExpand` of that of $u$, i.e. the substitution $q \mapsto q^p$. Given a place specialisation datum `Psp` for $(p, M, H, A)$ and a prolongation datum `Rpd` for `Psp` and $\theta_0$ — two regular prolongations $R_1, R_2$ of $A$ to $F_M$ with residues in the reduction function field over $\kappa$, such that $R_1$'s residue is coefficientwise reduction on $A$-integral series, and $R_2$'s integers are $\theta_0^{-1}$ of $R_1$'s with $R_2$-residue of $f$ equal to the $R_1$-residue of $\theta_0 f$ — the conclusion is: for every $v \in F_{M/p}$ and every pair of proofs that $\alpha v$ lies in the integers of $R_1$ and of $R_2$, the $R_2$-residue of $\alpha v$ equals `qExpFrobeniusModL` (the endomorphism $q \mapsto q^p$ of the mod-$p$ $q$-expansion function field over $\kappa$ for the subgroup `ΓN p M H hpM`) applied to the $R_1$-residue of $\alpha v$.
--
--   This is the $q$-expansion form of the Eichler–Shimura congruence relation at a prime exactly dividing the level: on functions coming from level $M/p$, the two reductions attached to the pair of prolongations differ by the Frobenius substitution $q \mapsto q^p$. It feeds the construction of specialisation and prolongation data for $X_H$ at $p$, being used in the existence statement for such data with prescribed behaviour on the component group off the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.ProlongationDatum.residueSnd_alpha_eq_qExpFrobeniusModL_residueFst_of_qExpand
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))

    (θ₀ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ₀ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ₀ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ₀) :
    ∀ (v : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (h₁ : α v ∈ Rpd.R₁.integers) (h₂ : α v ∈ Rpd.R₂.integers),
      Rpd.R₂.residue ⟨α v, h₂⟩ = qExpFrobeniusModL (ResidueField ↥A) (ΓN p M H hpM) p (Rpd.R₁.residue ⟨α v, h₁⟩) := by sorry
