-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_orderLawFixed_of_prolongationDatum
-- name    : ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_orderLawFixed_of_prolongationDatum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/e62bf96d-95d0-5a77-a5e7-99e1ec0872a7
-- title:
--   Common node value at supersingular gluing pairs
-- statement:
--   Fix a prime $p$ and $M$ with $p \mid M$, $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, the hypothesis $\mathrm{hj}$ that the $q$-expansion `jqModC ℚ` lies in the full-level $q$-expansion function field, and a Deligne–Rapoport datum $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R_p \to A$ lifting the structure map to $\overline{\mathbb{Q}}$. Further data: a unit $pb$ of $\mathbb{Z}/(M/p)$ represented by $p$; the map $\delta$ on places of $\mathrm{Fbar} =$ the $q$-expansion function field over $\kappa$ at level $\Gamma_N$, given by the diamond automorphism `diamondActionModL` at $pb$ acting through `SemilinearAut.ofAlgAut`; a finset $SS$ whose members are exactly the pairs $(s_1,s_2)$ with $s_2$ supersingular and $s_1$ its Frobenius pullback; an automorphism $\theta$ of $\mathrm{FM} =$ `xHFunctionFieldBar M H` realising, via $\mathrm{hwgen}$, the action of $\mathfrak{X}.w$ on places; an integral $\overline{\mathbb{Q}}$-algebra map $\alpha$ from level $M/p$ to level $M$ which is the identity on Laurent coefficients, with $\theta \circ \alpha$ integral; a specialisation $Psp$ of places and a prolongation datum $Rpd$ for $(Psp,\theta)$, consisting of regular prolongations $R_1,R_2$ of $A$ to $\mathrm{FM}$ with values in $\mathrm{Fbar}$, compatible with $q$-expansion reduction and linked by $R_2 = R_1 \circ \theta$; the compatibility $\mathrm{hcomp}$ identifying, for $i \in \{0,1\}$, the place of a closed point of the special fibre curve model lying over the reduction of an $A$-point with $Psp.\mathrm{reduceFst}\,\alpha$ respectively $Psp.\mathrm{reduceSnd}\,(\theta\circ\alpha)\,\delta$ applied to the corresponding characteristic-zero place; and the order law $\mathrm{hO} : Rpd.\mathrm{OrderLawFixed}\,\alpha\,(\theta\circ\alpha)\,\delta$. The conclusion: for every $f \in \mathrm{FM}$ lying in the integers of both $R_1$ and $R_2$, and every $s \in SS$ such that $\mathrm{ord}_V f \ge 0$ for each place $V$ of $\mathrm{FM}$ over $\overline{\mathbb{Q}}$ with $Psp.\mathrm{reduceFst}\,\alpha\,V = s_1$, there exists $c \in \kappa$ such that the residue of $f$ under $R_1$ lies in the valuation ring of $s_1$ with value $c$, and the residue of $f$ under $R_2$ lies in the valuation ring of $s_2$ with value $c$.
--
--   This is the node-value bridge for the Deligne–Rapoport fibre of $X_H(M)$ at $p \parallel M$: a modular function integral for both branch prolongations and regular above the first reading of a supersingular gluing pair takes one and the same value on the two branches meeting at the node. It is the node clause feeding [`ModularCurve.XHDRModelAtP.regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum`](thm.html#ModularCurve.XHDRModelAtP.regularityLaw_of_orderLawFixed_of_typeDichotomy_of_prolongationDatum).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_exists_hasValue_residue_pair_of_mem_ssNodePairs_of_orderLawFixed_of_prolongationDatum.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.XHDRModelAtP.exists_hasValue_residue_pair_of_mem_ssNodePairs_of_orderLawFixed_of_prolongationDatum
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hcomp : ∀ (i : Fin 2)
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
      (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
      (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
        if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
        else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ) :
    ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers), ∀ s ∈ SS,
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα V = s.1 → 0 ≤ V.ord f) →
      ∃ c : ResidueField ↥A,
        s.1.HasValue (Rpd.R₁.residue ⟨f, h₁⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c ∧
        s.2.HasValue (Rpd.R₂.residue ⟨f, h₂⟩ : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c := by sorry
