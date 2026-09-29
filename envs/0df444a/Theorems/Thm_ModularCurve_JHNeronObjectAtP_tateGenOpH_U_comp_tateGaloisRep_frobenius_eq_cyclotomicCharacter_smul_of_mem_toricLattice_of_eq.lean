-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
-- name    : ModularCurve.JHNeronObjectAtP.tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/f36b1309-a801-5389-b08c-0e77b965e456
-- title:
--   Uₚ and Frobenius on the toric lattice at ℓ=p
-- statement:
--   Fix a prime $p$ and a level $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is $1$. Assumed are: the $q$-expansion `jqModC ℚ` lies in the level-$\top$ $q$-expansion function field; a Deligne–Rapoport type model $\mathfrak{X}$ of `XHDRModelAtP p M H hpM hj`; an automorphism $\theta$ of $\overline{\mathbb{Q}}$-function field `xHFunctionFieldBar M H` which on Laurent series sends elements coming from level $M/p$ to their $q \mapsto q^p$ expansion `qExpand … p`; a compatibility `hwgen` saying that on $\overline{\mathbb{Q}}$-points of $\mathfrak{X}.\mathrm{Meta}$ the map $\mathfrak{X}.w.\mathrm{hom}$ induces the place-action of $\theta$; a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit, residue field of characteristic $p$ and algebraically closed, and a lift $\rho : R_p \to A$ of the structure map; level data $\Lambda$ with $\Lambda.\sigma_A$ induced by $\rho$ and $\Lambda.f$ smooth and proper with connected fibres carrying a group law; a Néron object $O$ over $(\Lambda, A)$ whose designation $(O.G, O.g, \text{unit section})$ represents the relative Picard subfunctor cut out by fibrewise algebraically trivial bundles on the model curve with section $\mathfrak{X}.\varepsilon_{\inf}$; the Hecke–diamond input predicate for $(M,H)$. Further, $\ell$ is a prime with $\ell = p$, and $T^t \le T_\ell(J_H(M))$ is a $\mathbb{Z}_\ell$-submodule characterised by: $x \in T^t$ exactly when every projection $x_n$ lies in $O.\mathrm{toricPts}(\ell^n)$. Two further inputs describe the special fibre: `hTOR`, that for any permutation of $O.\mathrm{ssFinset}$ inducing the mod-$p$ Frobenius on both place coordinates, any Frobenius element $\varphi$ at $A$ over $p$ in the decomposition subgroup, and any point $x$ with sections $s, s'$ over $\Lambda.\sigma_A$ representing $x$ and $\varphi \cdot x$, the node-unit datum $w$ of $s$ passes to $t \mapsto p \cdot w(\mathrm{perm}^{-1} t)$ for $s'$; and a permutation $\sigma_N$ of $O.\mathrm{ssFinset}$ sending the second place of $\sigma_N(n)$ to the first place of $n$, through which the Hecke operator $U_p$ acts on node units by $w \mapsto w \circ \sigma_N$. Finally $\varphi$ is an automorphism of $\overline{\mathbb{Q}}$ over $\mathbb{Q}$ which is a Frobenius at $A$ for $p$ and lies in the decomposition subgroup. The conclusion: for every $x \in T^t$, the Galois action $\rho_\ell(\varphi)x$ again lies in $T^t$, and both $U_p(\rho_\ell(\varphi)x)$ and $\rho_\ell(\varphi)(U_p x)$ equal $\chi_{\mathrm{cyc},\ell}(\varphi) \cdot x$, the cyclotomic character value regarded as a scalar in $\mathbb{Z}_\ell$.
--
--   This is the case $\ell = p$ of the description of the $U_p$-action on the toric part of the $\ell$-adic Tate module of $J_H(M)$ at a prime $p$ exactly dividing the level: on that part $U_p$ and arithmetic Frobenius are mutually inverse up to the cyclotomic character, which is the local input for level lowering at $p$. It is used in the constructions of the toric and old lattices in the Tate module of $J_1$ and in the statement about degeneracy maps and the inertia augmentation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
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

theorem ModularCurve.JHNeronObjectAtP.tateGenOpH_U_comp_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_mem_toricLattice_of_eq
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
    (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    (S : Set ℕ) (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ = p)
    (Tt : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))

    (hTOR : ∀ (perm : Equiv.Perm ↥O.ssFinset)
      (hperm : ∀ t : ↥O.ssFinset,
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).1 ∧
        ((perm t : ↥O.ssFinset) : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
            Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2 =
          qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
            (t : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) ×
              Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))).2)
      (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ)
      (x : JH M H) (s s' : SchemeHomOver Λ.σA O.g)
      (hs : (O.pts x).1 = barPt A ≫ s.1) (hs' : (O.pts (φ • x)).1 = barPt A ≫ s'.1)
      (w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ)
      (hw : O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.nodeUnit O.ssFinset w),
      O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s') = GluedPic0.nodeUnit O.ssFinset (fun t => p • w (perm.symm t)))

    (σN : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσN : ∀ n : ↥O.ssFinset, (σN n).1.2 = n.1.1)
    (hUPtor : ∀ w : ↥O.ssFinset → Additive (ResidueField ↥A)ˣ,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp (GluedPic0.nodeUnit O.ssFinset w))
          (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))) =
        GluedPic0.nodeUnit O.ssFinset (w ∘ σN))

    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : A.IsFrobeniusAt φ p) (hφD : φ ∈ A.decompositionSubgroup ℚ) :
    ∀ x ∈ Tt,
      JH.tateGaloisRep M H ℓ φ x ∈ Tt ∧
      tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) (JH.tateGaloisRep M H ℓ φ x) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x ∧
      JH.tateGaloisRep M H ℓ φ (tateGenOpH M H S ℓ (CohCarrier.Gen.U p (Fact.out) hpM) x) =
        ((cyclotomicCharacter (AlgebraicClosure ℚ) ℓ φ.toRingEquiv : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • x := by sorry
