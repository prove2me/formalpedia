-- Prove2me | Theorems.Thm_ModularCurve_DRModelPackageLevel_placeOfPoint_eq_reduce_of_isModel_of_orderLawFixed
-- name    : ModularCurve.DRModelPackageLevel.placeOfPoint_eq_reduce_of_isModel_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.564058+00:00
-- url     : https://prove2.me/theorems/7e1d2a34-7432-5c76-ab9a-84e60ca3f5f5
-- title:
--   Strict places reduce to reduceFst, reduceSnd on the Deligne–Rapoport model
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $p$ prime and $p \nmid N_0$, a package $\mathfrak{P}$ of type `DRModelPackageLevel N₀ p hpN₀` (a proper, flat, integral, locally finitely presented and normal model `X N₀ p` over `R p` together with a curve model $\mathfrak{P}.\mathrm{Meta}$ of the modular function field over $\overline{\mathbb{Q}}$, an isomorphism $\mathfrak{P}.\mathrm{eeta}$ onto the generic fibre, Galois and Igusa-chart compatibilities, and the further structural data of that structure), a valuation subring $A \subseteq \overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, and a ring map $\rho : R_p \to A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb{Q}}$ is the structure map; the residue field $\kappa_A$ then has characteristic $p$. Let `data` be modular polynomial data at level $p$ (a monic $\Phi \in \mathbb{Z}[X][X]$ of degree $\psi(p)$ annihilating the pair $(j, j_p)$), `hKr` the Kronecker congruence $\Phi \bmod p = (X^p - Y)(X - Y^p)$, and $h_\alpha$, $h_\beta$ the integrality of the two Hecke embeddings `heckeAlphaBar`, `heckeBetaBar`. Let $P$ be a place specialisation of $A$ at level $N_0$ into $\kappa_A$ along the residue map, carrying a prolongation tuple $R$ which satisfies `R.IsModel` (the two divisor laws and the two cusp laws) and `R.OrderLawFixed`. The conclusion is a conjunction of two assertions of the same shape. In each, one is given a $\overline{\mathbb{Q}}$-point $y$ of $\mathfrak{P}.\mathrm{Meta}.C$ sectioning its structure map, an $A$-point $u$ of `X N₀ p` over `Spec` $\rho$ with $u$ restricted to $\overline{\mathbb{Q}}$ equal to $y$ followed by $\mathfrak{P}.\mathrm{eeta}$ and the first pullback projection, a $\kappa_A$-point $u_\kappa$ of the fibre `fibre ((residue A).comp ρ)` which reduces $u$ and sections the fibre structure map, and the hypothesis that the place $\mathfrak{P}.\mathrm{Meta}.\mathrm{pointEquivPlace}\,y$ satisfies `P.IsStrictFst` or `P.IsStrictSnd`, i.e. geometric-level Frobenius carries $P.\mathrm{reduceFst}$ of it to $P.\mathrm{reduceSnd}$ of it (respectively the reverse) while its square moves the relevant place. Then: for every closed point $P_0$ of the curve $(\mathfrak{P}.\mathrm{Mfib}\,\kappa_A\,((\text{residue }A)\circ\rho)).C$ whose image under $\mathfrak{P}.\mathrm{efib}$ is the image of the closed point of $\kappa_A$ under $u_\kappa$ followed by `fibreMap0 𝔓.π`, the place attached to $P_0$ by that curve model equals $P.\mathrm{reduceFst}$ of the place of $y$; and for every closed point $P_1$ whose image under $\mathfrak{P}.\mathrm{efib}$ is the image of the closed point under $u_\kappa$ followed by the fibre map of $\mathfrak{P}.w$ and then `fibreMap0 𝔓.π`, the place attached to $P_1$ equals $P.\mathrm{reduceSnd}$ of the place of $y$. Here $P.\mathrm{reduceFst}$ and $P.\mathrm{reduceSnd}$ are $P.\mathrm{sp}$ applied to the restrictions of a place of the modular function field along `heckeAlphaBar`, respectively `heckeBetaBar`.
--
--   This is the dictionary, on the Deligne–Rapoport model of $X_0(N_0p)$ in characteristic $p$, between the two geometric reductions of a strict place of the modular function field and the two branches of the special fibre, read off through the degeneracy map $\pi$ and through the Atkin–Lehner involution. It is used in the analysis of points and divisors on the special fibre that feeds the Jacobian and level-lowering arguments, being cited by [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub) and by [`ModularCurve.DRModelPackageLevel.not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter`](thm.html#ModularCurve.DRModelPackageLevel.not_isStrict_and_reduceFst_mem_of_range_subset_range_comp_inter).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_DRModelPackageLevel_placeOfPoint_eq_reduce_of_isModel_of_orderLawFixed.lean

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra IsLocalRing
  ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

theorem ModularCurve.DRModelPackageLevel.placeOfPoint_eq_reduce_of_isModel_of_orderLawFixed
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (R : PlaceSpecialization.ProlongationTuple P) (_ : R.IsModel) (_ : R.OrderLawFixed),
    (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y)) ∧
    (∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).C),
          (𝔓.efib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over ((IsLocalRing.residue ↥A).comp ρ) ≫ fibreMap0 𝔓.π ((IsLocalRing.residue ↥A).comp ρ)).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ)).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y)) := by sorry
