-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
-- name    : ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/65c685ad-5470-5fd1-aa51-08fd1686d233
-- title:
--   Bounded exponent for the degeneracy push–pull kernel on torsion
-- statement:
--   Fix a prime $p$ and $M \ne 0$ with $p \mid M$ but $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that maps to $1$ under `ZMod.unitsMap` for $M/p \mid M$, and $M/p \ne 0$; assume $j$, as a Laurent series `jqModC ℚ`, lies in `qExpFunctionFieldC ℚ ⊤`. The data consist of: an integral model $\mathfrak{X}$ at $p$ for level $H$ in $(\mathbb{Z}/M)^\times$ (`XHDRModelAtP`), whose field `Meta` is a curve model over $\overline{\mathbb{Q}}$ with function field `xHFunctionFieldBar M H`; an automorphism $\theta$ of that field over $\overline{\mathbb{Q}}$ which on the level-$M/p$ subfield for `infSubgroup p M H hpM` (the image of $H$ in $(\mathbb{Z}/(M/p))^\times$) acts by $q \mapsto q^p$, i.e. by `qExpand _ p` on Laurent expansions, together with the hypothesis `hwgen` that the self-map $\mathfrak{X}.w$ moves $\overline{\mathbb{Q}}$-points of `Meta.C` by the semilinear automorphism `SemilinearAut.ofAlgAut θ` on places; a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit, algebraically closed residue field of characteristic $p$, and a lift $\rho : R p \to A$ of the structure map to $\overline{\mathbb{Q}}$; level data $\Lambda$ at level $M/p$ with $\Lambda.\sigma_A$ induced by $\rho$, satisfying the abelian-scheme bundle (smooth, proper, connected fibres, relative group law) and with `pts`, `ptsSp` additive for the relative group law; a Néron object $O$ at level $M$ whose designation $(O.G, O.g, \text{unit section})$ represents the relative $\mathrm{Pic}^0$ subfunctor cut out by `algEquivZeroCut` for the model's structure morphism and section $\mathfrak{X}.\varepsilon_{\inf}$; endomorphisms $F$, $F^{-1}$, $F^{*}$ of $\mathrm{Pic}^0$ of `Fbar p M H hpM` over the residue field of $A$, with $F$ the Frobenius push-forward `qExpFrobeniusPushforwardModL` at $p$, $F^{-1}$ a two-sided inverse of $F$, and $F^{*} = p\,F^{-1}$; a unit $pb$ of $\mathbb{Z}/(M/p)$ reducing to $p$ and the diamond endomorphism $\delta$ it induces through `diamondActionModL`; and two homomorphisms $\alpha^{*}_i : J_{H'}(M/p) \to J_H(M)$ together with morphisms $\mathrm{degPull}_i$ from $\Lambda$'s scheme to $O.G$ over the base, which are group-law homomorphisms, carry $\Lambda.\mathrm{pts}(x)$ to $O.\mathrm{pts}(\alpha^{*}_i x)$ on generic points, and on the special fibre satisfy, after `GluedPic0.toPic0Pair` for $O$'s gluing set, $z \mapsto (z, F^{*} z)$ for $i = 0$ and $z \mapsto (F^{*} z, \delta z)$ for $i = 1$. The conclusion: there is an $N \ne 0$ such that for all $a, b \in J_{H'}(M/p)$ annihilated by a common positive integer, vanishing of $O.\mathrm{degPts}\,j\,(\alpha^{*}_0 a + \alpha^{*}_1 b)$ for both $j \in \{0,1\}$ forces $N \cdot a = 0$ and $N \cdot b = 0$.
--
--   This is the torsion form of Ribet's statement that the push–pull composite of the two degeneracy maps between level $M/p$ and level $M$ (the matrix with diagonal entries $p+1$ and off-diagonal Hecke entries at $p$) is an isogeny: its kernel on torsion has exponent bounded by a single integer $N$, obtained here from the Eichler–Shimura description of the degeneracy maps on the special fibre rather than from bounds on Hecke eigenvalues. It feeds the separation of the old part from the toric part of the Tate module at $p$, used in level lowering when $p$ exactly divides the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_nsmul_eq_zero_of_forall_degPts_pull_add_pull_eq_zero
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
    ∃ N : ℕ, N ≠ 0 ∧ ∀ a b : JH (M / p) (infSubgroup p M H hpM),
      (∃ m : ℕ, 0 < m ∧ m • a = 0 ∧ m • b = 0) →
      (∀ j : Fin 2, O.degPts j (αpull 0 a + αpull 1 b) = 0) → N • a = 0 ∧ N • b = 0 := by sorry
