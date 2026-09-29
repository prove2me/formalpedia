-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
-- name    : ModularCurve.XHDRModelAtP.divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/c947aeab-5260-5384-97af-75ef09398d7f
-- title:
--   Second divisor law from the first at p ∥ M
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbb{Z}/M)^\times$ contain every unit that becomes $1$ in $(\mathbb{Z}/(M/p))^\times$, and let $j$ lie in the $q$-expansion function field of full level over $\mathbb{Q}$; let $\mathfrak{X}$ be a model datum `XHDRModelAtP p M H hpM hj`. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, with algebraically closed residue field $\kappa$ of characteristic $p$, and let $\rho : R_p \to A$ be a ring homomorphism compatible with the structure map $R_p \to \overline{\mathbb{Q}}$. Write $F_M =$ `xHFunctionFieldBar M H`, $F_{M/p}$ for the corresponding field at level $M/p$ with the image subgroup `infSubgroup p M H hpM`, and $\bar F =$ `JHNeronObjectAtP.Fbar p M H hpM κ`. Let $pb \in (\mathbb{Z}/(M/p))^\times$ have underlying element $p$, and let $\delta$ act on places of $\bar F$ by the semilinear automorphism attached to the diamond automorphism `diamondActionModL` at $pb$ via [`CuspForm.gammaLift`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36). Let $\theta$ be an $\overline{\mathbb{Q}}$-automorphism of $F_M$ such that any two $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}.C$ related by $\mathfrak{X}.w$ after $\mathfrak{X}.\mathtt{eeta}$ followed by the first pullback projection have places related by `SemilinearAut.ofAlgAut θ`. Let $\alpha : F_{M/p} \to F_M$ be an $\overline{\mathbb{Q}}$-algebra map inducing the identity on underlying Laurent series, with $\alpha$ and $\theta \circ \alpha$ integral. Given a specialisation datum $Psp$ and a prolongation datum $Rpd$ for $Psp$ and $\theta$, assume: (i) for every $f$ in the integers of both $Rpd.R_1$ and $Rpd.R_2$ with both residues nonzero there is $g \neq 0$ in $\bar F$ whose order function is the $Psp.\mathrm{sp}$-pushforward of the divisor of the norm of $f$ along $\alpha$, and which satisfies $\mathrm{ord}_{\Phi u}(g) = \mathrm{ord}_{\Phi u}(\bar f_1) + \mathrm{ord}_u(\bar f_2)$ for all places $u$, where $\Phi =$ `qExpFrobeniusPlaceModL κ (ΓN p M H hpM) p`; (ii) the first divisor law `Rpd.DivisorLawFst` for $\alpha, \theta \circ \alpha, \delta$; (iii) the type dichotomy `Psp.TypeDichotomy` for the same data; (iv) $\delta \circ \Phi = \Phi \circ \delta$ on places. Then the second divisor law `Rpd.DivisorLawSnd` holds: for every $f$ in both rings of integers with nonzero residues, every divisor $D$ on $F_M$ with $D(W) = \mathrm{ord}_W(f)$, and every place $v$ of $\bar F$ not satisfying `Fixed` for $\delta$, the pushforward of $Psp.\mathrm{sndDiv}$ applied to $D$ along $Psp.\mathrm{reduceSnd}$ takes at $v$ the value $\mathrm{ord}_v$ of the residue of $f$ in $Rpd.R_2$.
--
--   This is one of the two divisor laws required of the prolongation datum attached to the reduction of $X_H(M)$ at a prime $p$ exactly dividing $M$: it transfers the known behaviour of divisors on the first branch to the second, using the reduction of the norm along $\alpha$ and the dichotomy classifying how places reduce on the two branches. It feeds into [`ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_jHPlaceSpecialization_prolongationDatum_gluedSpecialization_componentGroup_offDiag_of_wgen), which assembles the specialisation and prolongation data together with the description of the component group away from the diagonal.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_RatFuncPlaces

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRModelAtP.divisorLawSnd_prolongationDatum_of_divisorLawFst_of_norm_of_typeDichotomy
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

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hN : ∀ (f : ↥(xHFunctionFieldBar M H)) (h₁ : f ∈ Rpd.R₁.integers) (h₂ : f ∈ Rpd.R₂.integers),
        Rpd.R₁.residue ⟨f, h₁⟩ ≠ 0 → Rpd.R₂.residue ⟨f, h₂⟩ ≠ 0 →
        letI := algebraAlong α
        ∃ g : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A), g ≠ 0 ∧
          (∀ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
            (∀ V, D V = V.ord (Algebra.norm ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) f)) →
            ∀ v', Finsupp.mapDomain Psp.sp D v' = v'.ord g) ∧
          ∀ u : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord g =
              (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p u).ord (Rpd.R₁.residue ⟨f, h₁⟩) +
                u.ord (Rpd.R₂.residue ⟨f, h₂⟩))
    (hDF : Rpd.DivisorLawFst α (θ.toAlgHom.comp α) hα hβ δ)
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hcomm : ∀ v, δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p v) = qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p (δ v)) :
    Rpd.DivisorLawSnd α (θ.toAlgHom.comp α) hα hβ δ := by sorry
