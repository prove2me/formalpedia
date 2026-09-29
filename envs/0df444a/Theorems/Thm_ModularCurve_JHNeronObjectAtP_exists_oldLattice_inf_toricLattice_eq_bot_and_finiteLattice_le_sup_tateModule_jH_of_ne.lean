-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
-- name    : ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/7117c5a7-d02d-525f-96c2-2fdbf32bbfc3
-- title:
--   p-old lattice in T_ℓ J_H(M) for p ∥ M
-- statement:
--   Fix a prime $p$ and $M\ge 1$ with $p\mid M$, $p^2\nmid M$ and $M/p\neq 0$, and a subgroup $H\le(\mathbb{Z}/M)^\times$ containing every unit whose image under reduction to $(\mathbb{Z}/(M/p))^\times$ is $1$; write $H'=$ `infSubgroup p M H hpM` for the image of $H$. Assume $j$ lies in the $q$-expansion function field of $\mathrm{SL}_2(\mathbb{Z})$, fix integral model data $\mathfrak{X}$ of type `XHDRModelAtP p M H hpM hj`, and an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of `xHFunctionFieldBar M H` which on $q$-expansions sends any element agreeing with a level-$(M/p)$ element $u$ to `qExpand` of $u$ by $p$, together with `hwgen`, saying that the automorphism $\mathfrak{X}.w$ of the model induces $\theta$ on places of geometric points. Fix a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit, algebraically closed residue field $\kappa$ of characteristic $p$, a ring map $\rho:R_p\to A$ compatible with $R_p\to\overline{\mathbb{Q}}$, level data $\Lambda$ for $J_{H'}(M/p)$ over `base p` with $\Lambda.\sigma_A=\mathrm{Spec}\,\rho$ whose point dictionaries are additive (`hΛpts_add`, `hΛptsSp_add`) and whose structure map is smooth, proper with connected fibres and carries a relative group law, and an object $O$ of type `JHNeronObjectAtP p M H hpM A hA Λ` for $J_H(M)$ whose Picard property is recorded by `hD`: $(O.G,O.g)$ with its unit section represents the relative sub-Picard functor of $\mathfrak{X}$ cut out by fibrewise algebraic triviality. Fix a prime $\ell\neq p$ and $\mathbb{Z}_\ell$-submodules $T^t,T^f$ of [`TateModule ℓ (JH M H)`](def/EllipticCurve_TateModule.html#L15) consisting of those compatible systems all of whose $n$-th components lie in `O.toricPts (ℓ^n)`, respectively `O.finPts (ℓ^n)`. On $\mathrm{Pic}^0$ of the reduction `Fbar p M H hpM κ`, let $F$ be the $q$-expansion Frobenius pushforward `qExpFrobeniusPushforwardModL` at $p$, $\mathrm{Finv}$ a two-sided inverse of $F$, $F^*=p\cdot\mathrm{Finv}$, and $\delta$ the action of the diamond automorphism attached to a unit $\mathrm{pb}$ of $\mathbb{Z}/(M/p)$ reducing to $p$. Finally assume given two additive maps $\alpha_0,\alpha_1:J_{H'}(M/p)\to J_H(M)$ induced by maps $\mathrm{degPull}\,i$ of schemes over `base p` from $\Lambda.X$ to $O.G$ which are compatible with the relative group laws, such that on the special fibre the pair of classes attached to $\mathrm{degPull}\,0$, respectively $\mathrm{degPull}\,1$, applied to a point with class $z$ is $(z,F^*z)$, respectively $(F^*z,\delta z)$, and a $\mathbb{Z}_\ell$-linear reduction map $\mathrm{red}:T^f\to T_\ell(\mathrm{Pic}^0\times\mathrm{Pic}^0)$ computing levelwise the pair of classes of the special fibre of a point and with kernel exactly $T^t$. Then there is a $\mathbb{Z}_\ell$-submodule $T^{\mathrm{old}}$ of [`TateModule ℓ (JH M H)`](def/EllipticCurve_TateModule.html#L15) consisting exactly of the systems of the form $\alpha_0(w_0)+\alpha_1(w_1)$, levelwise, for $w_0,w_1$ in the Tate module of $J_{H'}(M/p)$, such that $T^{\mathrm{old}}\le T^f$, $T^{\mathrm{old}}\cap T^t=0$, and for some $k$ one has $\ell^k x\in T^{\mathrm{old}}+T^t$ for every $x\in T^f$.
--
--   This is the Tate-module form of Ribet's description of the reduction at $p$ of $J_H(M)$ when $p$ exactly divides $M$: the $p$-old lattice, cut out by the two degeneracy pull-backs from level $M/p$, sits inside the finite part, meets the toric part trivially, and together with the toric part exhausts the finite part up to bounded $\ell$-power torsion. It feeds the statement that an inertia-generated submodule contains a bounded multiple of the finite part modulo the $p$-old part, which is the geometric input for lowering the level at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.lean

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

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice
open AlgebraicCurve

open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
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
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

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

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

    (red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hred_pin : ∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
      TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s)))
    (hred_ker : ∀ x : ↥Tf, red x = 0 ↔ (x : TateModule ℓ (JH M H)) ∈ Tt) :
    ∃ Told : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)),

      (∀ x : TateModule ℓ (JH M H), x ∈ Told ↔
        ∃ w₀ w₁ : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
          TateModule.proj ℓ (JH M H) n x =
            αpull 0 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
              αpull 1 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₁)) ∧

      Told ≤ Tf ∧

      Told ⊓ Tt = ⊥ ∧

      ∃ k : ℕ, ∀ x ∈ Tf, (((ℓ : ℕ) : ℤ_[ℓ]) ^ k) • x ∈ Told ⊔ Tt := by sorry
