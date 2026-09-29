-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
-- name    : ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/840f0f6e-f419-5d5d-912e-dbe632776dca
-- title:
--   Diamond ⟨ d⟩ acts on the glued special fibre by glueMap
-- statement:
--   Fix a prime $p$, a natural number $M$ with $p \mid M$ and $M/p \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and the hypothesis $hj$ that the $q$-expansion $jqModC\ \mathbb{Q}$ lies in the function field $qExpFunctionFieldC\ \mathbb{Q}$ of full level. Let $\mathfrak{X}$ be an `XHDRModelAtP p M H hpM hj`, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit in $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$, let $\Lambda$ be level data and $O$ a `JHNeronObjectAtP p M H hpM A hA Λ`, and let $\rho : R p \to A$ satisfy $A.\mathrm{subtype} \circ \rho =$ the structure map to $\overline{\mathbb{Q}}$, with $\Lambda.\sigma A = \operatorname{Spec}\rho$. Two dictionary hypotheses are assumed, summarised here. First, `hsp`: for each $i \in \{0,1\}$, given geometric points $y_1, y_2$ of $\mathfrak{X}.\mathrm{Meta}.C$ over the base, sections $u_1, u_2$ of `toBase p (ΓM M H) hj` over $\operatorname{Spec}\rho$ whose base change along `barPt A` is $y_j$ followed by $\mathfrak{X}.\mathrm{eeta}$ and the first projection and whose topological image lies in $\mathfrak{X}.\mathrm{smoothLocus}$, sections $u\kappa_1, u\kappa_2$ of the fibre over $\kappa$ reducing $u_1, u_2$ and splitting the second projection, closed points $P_1, P_2$ of $(\mathfrak{X}.\mathrm{Mfib}\ A\ hA\ \rho\ h\rho).C$ whose images under $\mathfrak{X}.\mathrm{efib}$ followed by $\mathfrak{X}.\mathrm{comp}\ i$ are the closed points of $u\kappa_1, u\kappa_2$, a degree-zero divisor $Dv$ on $\overline{\mathbb{Q}}$-places of $xHFunctionFieldBar\ M\ H$ equal to $[y_1] - [y_2]$ under `pointEquivPlace`, and an admissible gluing datum $x$ for $O.\mathrm{ssFinset}$ whose first divisor component is $[P_1] - [P_2]$ if $i = 0$ and $0$ otherwise, whose second is $[P_1] - [P_2]$ if $i = 1$ and $0$ otherwise, and whose unit component vanishes, there exists a section $s$ of $O.g$ over $\Lambda.\sigma A$ with $O.\mathrm{pts}$ of the class of $Dv$ equal to `barPt A` followed by $s$, and with $O.\mathrm{ptsSp}^{-1}$ of the restriction of $s$ along `resPt A` equal to the glued class of $x$. Second, `hdia0`: for every $e \in (\mathbb{Z}/(M/p))^{\times}$ and every closed point $P$, the transport of $P$ through the inverse of $\mathfrak{X}.\mathrm{efib}$, the fibre map of the isomorphism $\mathfrak{X}.\mathrm{dia0}\ e$, and $\mathfrak{X}.\mathrm{efib}$ is again a closed point, and its place is the image of the place of $P$ under the semilinear automorphism `ofAlgAut` of $diamondActionModL\ \kappa\ (M/p)\ (infSubgroup\ p\ M\ H\ hpM)$ evaluated at $gammaLift\ (M/p)\ e$. Finally, let $S \subseteq \mathbb{N}$, $d \in (\mathbb{Z}/M)^{\times}$, and let $hstab$ assert that the semilinear automorphism $g$ obtained in the same way from the image of $d$ in $(\mathbb{Z}/(M/p))^{\times}$ is node-stable for $O.\mathrm{ssFinset}$, i.e. carries each pair in that finset to a pair again in it. The conclusion is that for every class $\xi$ in the glued degree-zero class group $GluedPic0\ \kappa\ (Fbar\ p\ M\ H\ hpM\ \kappa)\ O.\mathrm{ssFinset}$, conjugating the endomorphism $O.\mathrm{hecke}\ S\ \langle d\rangle$ by the bijection $O.\mathrm{ptsSp}$ — that is, composing the section $O.\mathrm{ptsSp}\ \xi$ with that endomorphism and applying $O.\mathrm{ptsSp}^{-1}$ — yields $GluedPic0.glueMap\ O.\mathrm{ssFinset}\ g\ hstab\ \xi$.
--
--   This identifies the action of the diamond operator $\langle d \rangle$ on the special fibre of the Néron object of $J_H(M)$ at a prime $p$ dividing $M$: under the dictionary between sections over the residue field and glued degree-zero divisor classes on the two components of the Deligne–Rapoport reduction, $\langle d \rangle$ acts by the glued semilinear action of the diamond at level $M/p$. It is used in the analysis of the Hecke operator $U_p$ on the special fibre, in particular in the comparison of $U_p$ with Frobenius and Verschiebung twisted by a diamond, and in the Galois-theoretic relation for $\langle d \rangle$ at a Frobenius element in the inertia subgroup.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.ptsSp_symm_schemeHomOverComp_hecke_dia_eq_glueMap
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt A ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib A hA ρ hρ).C)
      (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥A)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib A hA ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt A ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib A hA ρ hρ).C),
      ∃ h : (inv (𝔛.efib A hA ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥A).comp ρ)).base
            ((𝔛.efib A hA ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib A hA ρ hρ).C,
        (𝔛.Mfib A hA ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib A hA ρ hρ).placeOfPoint P)
    (S : Set ℕ) (d : (ZMod M)ˣ)
    (hstab : SemilinearAut.IsNodeStable O.ssFinset
      (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
        (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d))))) :
    ∀ ξ : GluedPic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
      O.ptsSp.symm (schemeHomOverComp (O.ptsSp ξ) (O.hecke S (CohCarrier.Gen.dia d))) =
        GluedPic0.glueMap O.ssFinset
          (SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) (ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d)))) hstab ξ := by sorry
