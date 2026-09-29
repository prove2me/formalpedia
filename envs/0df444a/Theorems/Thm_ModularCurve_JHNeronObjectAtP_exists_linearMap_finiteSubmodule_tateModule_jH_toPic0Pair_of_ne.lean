-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
-- name    : ModularCurve.JHNeronObjectAtP.exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f9785f2f-c5e2-5f4c-a8e2-8f03c55e6869
-- title:
--   Reduction of the finite part of T_ℓ J_H(M) and Uₚ
-- statement:
--   Fix a prime $p$ and $M \neq 0$ with $p \mid M$ but $p^2 \nmid M$, and $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$. Assume $j$, as a Laurent series over $\mathbb{Q}$, lies in the $q$-expansion function field of level $\mathrm{SL}_2(\mathbb{Z})$, and let $\mathfrak{X}$ be an `XHDRModelAtP` datum for $(p,M,H)$. Let $\theta$ be an $\overline{\mathbb{Q}}$-algebra automorphism of $\overline{\mathbb{Q}}\cdot X_H$-function field which, on series coming from level $M/p$ with group `infSubgroup p M H hpM`, acts by $q \mapsto q^p$ (the map `qExpand` at $p$), and assume the degeneracy $\mathfrak{X}.w$ induces on $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}$ the place-action of $\theta$ via `SemilinearAut.ofAlgAut`. Let $A \subset \overline{\mathbb{Q}}$ be a valuation subring with $p$ a non-unit, residue field $\kappa$ algebraically closed of characteristic $p$, and $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb{Q}}$. Let $\Lambda$ be a `LevelData` over $A$ whose structure morphism is $\mathrm{Spec}\,\rho$ and whose $\Lambda.f$ is smooth and proper with connected fibres and a group law, and let $O$ be a `JHNeronObjectAtP` for these data, with $(O.G, O.g)$ together with the unit section representing the fibrewise algebraically trivial relative Picard functor of $\mathfrak{X}$ (the hypothesis `hD`). Let $S \subseteq \mathbb{N}$ and let $\ell \neq p$ be a prime, and let $T^t, T^f \subseteq T_\ell(J_H(M))$ be the $\mathbb{Z}_\ell$-submodules of those sequences all of whose $n$-th terms lie in $O.\mathrm{toricPts}(\ell^n)$, respectively $O.\mathrm{finPts}(\ell^n)$. On $\mathrm{Pic}^0$ of the special-fibre function field `Fbar p M H hpM κ` let $F$ be the Frobenius push-forward `qExpFrobeniusPushforwardModL` at $p$, assumed invertible with inverse $F^{-1}$, put $F^{*} = p\,F^{-1}$, and let $\delta$ be the semilinear action of the diamond automorphism attached to a unit $\bar p \in (\mathbb{Z}/(M/p))^\times$ lifting $p$. Assume finally that on the glued $\mathrm{Pic}^0$ of $O.\mathrm{ssFinset}$, composing with the Hecke section $U_p$ of $O$ corresponds, after `toPic0Pair`, to the block operator with entries $F^{*}$, $(p-1)\,\mathrm{id}$, $0$, $\delta \circ F$. Then there is a $\mathbb{Z}_\ell$-linear map $\mathrm{red} : T^f \to T_\ell(\mathrm{Pic}^0 \times \mathrm{Pic}^0)$ such that: whenever the $n$-th component of $x \in T^f$ has its generic section factoring as `barPt A` followed by a section $s$ of $O.g$ over $\Lambda.\sigma_A$, the $n$-th component of $\mathrm{red}\,x$ is the `toPic0Pair` image of the class corresponding to the reduction of $s$ along `resPt A`; $\mathrm{red}\,x = 0$ if and only if $x \in T^t$; $\mathrm{red}$ is surjective; and for $x \in T^f$ with $U_p x \in T^f$ one has $\mathrm{red}(U_p x)$ equal to the above block operator, acting through [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174), applied to $\mathrm{red}\,x$.
--
--   This is the Tate-module form, at a prime $p$ exactly dividing the level, of the description of the special fibre of the Néron object of $J_H(M)$: the finite part of $T_\ell J_H(M)$ maps onto the Tate module of a pair of copies of $\mathrm{Pic}^0$ of the special-fibre function field, with toric part as kernel, and $U_p$ becomes Ribet's upper-triangular block matrix $\begin{pmatrix} pF^{-1} & (p-1) \\ 0 & \langle \bar p\rangle F\end{pmatrix}$. It feeds the analysis of inertia at $p$ on $T_\ell J_H(M)$ used in level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
  AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_linearMap_finiteSubmodule_tateModule_jH_toPic0Pair_of_ne
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (S : Set ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

    (Tt Tf : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))
    (hTf : ∀ x : TateModule ℓ (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.finPts (ℓ ^ n))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (hUPabq : ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        GluedPic0.toPic0Pair O.ssFinset
            (O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM)))) =
          AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)
            (GluedPic0.toPic0Pair O.ssFinset ξ)) :
    ∃ red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),

      (∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
        (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
          GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s))) ∧

      (∀ x : ↥Tf, red x = 0 ↔ (x : TateModule ℓ (JH M H)) ∈ Tt) ∧

      Function.Surjective red ∧

      (∀ (x : ↥Tf) (hx : tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (x : TateModule ℓ (JH M H)) ∈ Tf),
        red ⟨tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (x : TateModule ℓ (JH M H)), hx⟩ =
          TateModule.rep ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) (AddMonoid.End (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
            (AlgebraicCurve.Pic0Pair.blockOp Fstar (((p : ℤ) - 1) • AddMonoidHom.id _) 0 (δ.comp F)) (red x)) := by sorry
