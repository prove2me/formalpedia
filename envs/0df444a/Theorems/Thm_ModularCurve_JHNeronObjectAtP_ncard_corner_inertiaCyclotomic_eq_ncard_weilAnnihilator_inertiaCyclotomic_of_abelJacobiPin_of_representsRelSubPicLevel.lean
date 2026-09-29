-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_ncard_corner_inertiaCyclotomic_eq_ncard_weilAnnihilator_inertiaCyclotomic_of_abelJacobiPin_of_representsRelSubPicLevel
-- name    : ModularCurve.JHNeronObjectAtP.ncard_corner_inertiaCyclotomic_eq_ncard_weilAnnihilator_inertiaCyclotomic_of_abelJacobiPin_of_representsRelSubPicLevel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/e292b69f-a50c-5598-bea7-5a8b5f881bbf
-- title:
--   Cyclotomic points of a Hecke corner and its Weil annihilator
-- statement:
--   Let $p$ be a prime with $p \neq 2$, let $M$ be a positive integer with $p \mid M$ and $p^2 \nmid M$, and let $H \leq (\mathbb{Z}/M)^\times$ contain every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial. Fix a set $S$ of naturals and the Hecke–diamond inputs `HeckeDiamondInputsHAll` for $(M,H)$, which assert the Hecke inputs along each prime $\ell$ over $\overline{\mathbb{Q}}$ together with, for each $d \in (\mathbb{Z}/M)^\times$, an $\overline{\mathbb{Q}}$-automorphism of the function field $\overline{F}_H$ realising the diamond operator. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting compatibly and faithfully on the Tate module $T_p J_H(M)$, and let `op` send each generator $T_\ell$, $U_q$, $\langle d\rangle$ to an element of $\mathbb{T}$ acting as the corresponding operator, with $\mathbb{Z}_p[\operatorname{im}(\mathrm{op})] = \mathbb{T}$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (a complete orthogonal family of idempotents $e_i$ with maximal ideals $\mathfrak{m}_i$ exhausting $\operatorname{Max}\mathbb{T}$ and $e_i \in \mathfrak{m}_j \iff i \neq j$) and let $i_0$ satisfy $\mathrm{op}(U_p) \notin \mathfrak{m}_{i_0}$. Let $Pl$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit and algebraically closed residue field of characteristic $p$. Further data: the integrality condition `hj` on the $q$-expansion of $j$, an integral model $\mathfrak{X}$ at $p$ of level $\Gamma_H(M)$, level data $\Lambda$ at level $M/p$ whose structure morphism is smooth and proper with connected fibres and a relative group law, the Néron object $O$ at $Pl$, and a package of representability and Abel–Jacobi pinning hypotheses (representability of the relative sub-Picard functor cut out by fibrewise triviality by the designation built from $O$, over the base and after base change to $\mathbb{Q}$, separatedness, comparison morphisms $ajQ$, $kQ$, $\overline{aj}$, a pinned cusp $\overline{\varepsilon}$, compatibilities of Poincaré bundles, additivity of $O.\mathrm{pts}$ for the relative group law, the divisor identity $(x)-(s)$ for the Abel–Jacobi map, and representability at level $\Gamma_N$), summarised here. Finally let $e$ be a divisorial Weil pairing datum for $\overline{F}_H$ at $p$ and $B : J_H(M) \times J_H(M) \to \overline{\mathbb{Q}}$ any map agreeing with $e.\mathrm{pair}$ on $p$-torsion. Call $x$ inertia-cyclotomic if $\sigma \cdot x = c\,x$ for every $\sigma$ in the inertia subgroup of $Pl$ over $\mathbb{Q}$ and every $c \in \mathbb{N}$ with $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^p = 1$. Then the set of inertia-cyclotomic points in the image under the first projection $T_p J_H(M) \to J_H(M)$ of the corner submodule $e_{i_0} \cdot T_p J_H(M)$ and the set of inertia-cyclotomic $y$ with $p\,y = 0$ satisfying $B(x,y) = 1$ for all $x$ in the corresponding image of $(1-e_{i_0})\cdot T_p J_H(M)$ have the same cardinality (as `Set.ncard`).
--
--   This is the counting step in the study of the $p$-torsion of $J_H(M)$ at a prime dividing the level exactly once: the cyclotomic (inertia-eigen) part of a Hecke corner $e_{i_0}J_H(M)[p]$ is matched numerically with the cyclotomic part of the Weil-pairing annihilator of the complementary corner, the annihilator playing the role of the adjoint corner. It is used in the construction of the perfect pairing between corner and adjoint corner and the ensuing toric-rank count at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_ncard_corner_inertiaCyclotomic_eq_ncard_weilAnnihilator_inertiaCyclotomic_of_abelJacobiPin_of_representsRelSubPicLevel.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve

open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.ncard_corner_inertiaCyclotomic_eq_ncard_weilAnnihilator_inertiaCyclotomic_of_abelJacobiPin_of_representsRelSubPicLevel
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥Pl) p] [IsAlgClosed (IsLocalRing.ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (ModularCurve.JZeroNeronObjectAtP.baseRing p) Λ.f)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)

    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ))
    (hsep : IsSeparated (baseChange (R p) (toBase p (ΓM M H) hj) ℚ))
    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).toBase)
    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (ajbar : 𝔛.Meta.C ⟶ O.G)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hpoinc : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst O.g (specMap (R p) ℚ), pullback.condition⟩)).L))
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (((⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))).baseChange ℚ).zeroSection)
    (hajQ : (∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
        ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
        ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
        (Category.comp_id t)))).idealModule)))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))
    (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst O.g (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ O.g = 𝔛.Meta.toBase ≫ genPt p)
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1)
    (hpts_law : (∀ x y : JH M H,
        O.pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (O.pts x) (O.pts y)))
    (hAJ : (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (O.pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar))

    (hrepΛ : Nonempty (RepresentsRelSubPic (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)
          (algEquivZeroCut (toBase p (XHDRLevel.ΓN p M H hpM) hj) (schemeHomOverComp 𝔛.εinf 𝔛.π)) (⟨Λ.X, Λ.f, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (Λ.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (XHDRLevel.ΓN p M H hpM) hj))))

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (e : DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) p)
    (B : JH M H → JH M H → AlgebraicClosure ℚ)
    (hB : ∀ (x y : JH M H) (hx : (p : ℤ) • x = 0) (hy : (p : ℤ) • y = 0),
      B x y = e.pair ⟨x, Pic0.mem_torsion.mpr hx⟩ ⟨y, Pic0.mem_torsion.mpr hy⟩)
    :
    Set.ncard {x : JH M H | x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) ∧
          (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
            (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • x = c • x)} =
      Set.ncard {y : JH M H | (p • y = 0 ∧ ∀ x : JH M H, x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (1 - S'.e i₀)).toAddSubgroup).map
          (TateModule.proj p (ModularCurve.JH M H) 1) → B x y = 1) ∧
          (∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
            (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • y = c • y)} := by sorry
