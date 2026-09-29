-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_self
-- name    : ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/66938366-9405-51f5-b4fe-b6984e445b8d
-- title:
--   The p-old lattice in Tₚ J_H(M) at p ∥ M
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$, $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$. Assume $j$ lies in the level-one $q$-expansion function field over $\mathbb{Q}$, and fix: an integral model datum $\mathfrak{X} :$ `XHDRModelAtP p M H hpM hj` at $p$; an automorphism $\theta$ of $\overline{\mathbb{Q}}$-function field `xHFunctionFieldBar M H` which, on elements coming from level $M/p$ with subgroup `infSubgroup p M H hpM`, acts as the substitution $q \mapsto q^p$ (`qExpand`), and which by `hwgen` describes on places the Atkin–Lehner map $\mathfrak{X}.w$; a valuation subring $A \subset \overline{\mathbb{Q}}$ with $p$ a nonunit and algebraically closed residue field of characteristic $p$; a ring map $\rho : R_p \to A$ compatible with $R_p \to \overline{\mathbb{Q}}$; level data $\Lambda$ at $A$ (with $\Lambda.\sigma_A$ induced by $\rho$) whose $\Lambda.f$ is smooth and proper with connected fibres and carries a relative group law, and whose two point dictionaries are additive; a Néron object $O$ for $J_H(M)$ over `base p` with $O.G, O.g$ representing the relative sub-Picard functor of the integral model cut out by fibrewise algebraic equivalence to zero. Let $T^t, T^f$ be the $\mathbb{Z}_p$-submodules of $T =$ [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15) of compatible sequences lying levelwise in $O.\mathrm{toricPts}(p^n)$, respectively $O.\mathrm{finPts}(p^n)$. Let $F$ be the mod-$p$ Frobenius pushforward on $\mathrm{Pic}^0$ of the level-$\Gamma_N$ function field over the residue field, $F^{-1}$ its two-sided inverse, $F^* = p\,F^{-1}$, and $\delta$ the semilinear diamond action of a unit $\bar{p}$ of $\mathbb{Z}/(M/p)$ lifting $p$. Finally, let $\alpha^*_0, \alpha^*_1 : J_H(M/p) \to J_H(M)$ be group homomorphisms realised by morphisms $\mathrm{degPull}\,i$ from $\Lambda$'s scheme to $O.G$ over the base, compatible with the group laws and with generic points, and whose effect on special-fibre sections is $z \mapsto (z, F^* z)$ for $i = 0$ and $z \mapsto (F^* z, \delta z)$ for $i = 1$ under the glued $\mathrm{Pic}^0$-pair map. The conclusion asserts the existence of a $\mathbb{Z}_p$-submodule $T^{\mathrm{old}} \le T$ consisting exactly of those $x$ for which there are $w_0, w_1 \in$ [`TateModule p (JH (M/p) …)`](def/EllipticCurve_TateModule.html#L15) with $x_n = \alpha^*_0(w_{0,n}) + \alpha^*_1(w_{1,n})$ for all $n$, such that $T^{\mathrm{old}} \le T^f$, $T^{\mathrm{old}} \cap T^t = 0$, and for some $k \in \mathbb{N}$ one has $p^k x \in T^{\mathrm{old}} + T^t$ for every $x \in T^f$.
--
--   This is the $p$-adic analogue, at the residue characteristic $p \parallel M$, of the toric/old splitting of the Tate module used in Ribet's level-lowering argument: the image of the two degeneracy maps from level $M/p$ lies in the finite part of $T_p J_H(M)$, is disjoint from the toric part, and together with it exhausts the finite part up to a bounded power of $p$. It feeds the statements about the degeneracy span and the toric and old lattices for $T_p J_1$ used in the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_self.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_self
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

    (Tt Tf : Submodule ℤ_[p] (TateModule p (JH M H)))
    (hTt : ∀ x : TateModule p (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.toricPts (p ^ n))
    (hTf : ∀ x : TateModule p (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj p (JH M H) n x ∈ O.finPts (p ^ n))

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
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y)))) :
    ∃ Told : Submodule ℤ_[p] (TateModule p (JH M H)),

      (∀ x : TateModule p (JH M H), x ∈ Told ↔
        ∃ w₀ w₁ : TateModule p (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
          TateModule.proj p (JH M H) n x =
            αpull 0 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
              αpull 1 (TateModule.proj p (JH (M / p) (infSubgroup p M H hpM)) n w₁)) ∧

      Told ≤ Tf ∧

      Told ⊓ Tt = ⊥ ∧

      ∃ k : ℕ, ∀ x ∈ Tf, (((p : ℕ) : ℤ_[p]) ^ k) • x ∈ Told ⊔ Tt := by sorry
