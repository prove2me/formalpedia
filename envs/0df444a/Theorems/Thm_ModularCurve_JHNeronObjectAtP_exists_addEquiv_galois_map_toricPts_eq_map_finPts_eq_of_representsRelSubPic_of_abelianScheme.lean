-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
-- name    : ModularCurve.JHNeronObjectAtP.exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/3225db70-f44c-5f5d-b198-0e2308df608a
-- title:
--   Transport between two Néron objects for J_H(M) at p ∥ M
-- statement:
--   Fix a prime $p$ and a positive integer $M$ with $p \mid M$ and $p^2 \nmid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and the hypothesis `hj` that the $q$-expansion `jqModC ℚ` of $j$ lies in the function field `qExpFunctionFieldC ℚ ⊤`. Let $\mathfrak{X}$ be an inhabitant of `XHDRModelAtP p M H hpM hj`, i.e. a Deligne–Rapoport-style integral model datum for $X_H(M)$ over $R_p = \mathbb{Z}_{(p)}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$, whose residue field is algebraically closed of characteristic $p$. Let $\Lambda, \Lambda'$ be two level data at $A$ and let $O$ (over $\Lambda$) and $O'$ (over $\Lambda'$) be two inhabitants of `JHNeronObjectAtP`, each consisting of a scheme $G$ over `base p` with a relative group law, a bijection of $J_H(M) = \mathrm{Pic}^0$ of the geometric function field of $X_H(M)$ with the generic-fibre sections, and the smoothness, separatedness, finite-type, surjectivity, fibre-connectedness, Hecke and toric/finite-part data recorded there. Assume further that each of $O$, $O'$, with the zero section supplied by the unit of its group law, represents the relative Picard functor of `toBase p (ΓM M H) hj` rigidified along $\mathfrak{X}.\varepsilon_{\inf}$ and cut out by the condition that the rigidified line bundle be fibrewise algebraically equivalent to zero, and that the level object $\Lambda'.f$ of the second datum is an abelian scheme over the base ring (smooth, proper, with connected fibres and a relative group law). Then there is an additive automorphism $e$ of $J_H(M)$ satisfying $e(\sigma \cdot x) = \sigma \cdot e(x)$ for all $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and all $x$, and such that for every $m > 0$ the subgroup $O'.\mathrm{toricPts}\,m$ is the image under $e$ of $O.\mathrm{toricPts}\,m$, and $O'.\mathrm{finPts}\,m$ is the image under $e$ of $O.\mathrm{finPts}\,m$. No Hecke-equivariance of $e$ is asserted.
--
--   This is the uniqueness, or transport, statement for the Néron-object-of-record data attached to $J_H(M)$ at a prime exactly dividing the level: two such data over the same model are matched by a single Galois-equivariant automorphism of the group of points which identifies the toric and the finite parts in each level $m$. It is used in the analysis of the inertia action on torsion, in the statements `smul_sub_mem_toricPts_of_mem_inertia_of_abelJacobiPin_of_wgen` and `smul_sub_mem_toricPts_of_mem_inertia_of_representsRelSubPic_of_atkinLehner`, which need the toric part of one datum to be available from another.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_addEquiv_galois_map_toricPts_eq_map_finPts_eq_of_representsRelSubPic_of_abelianScheme
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (Λ' : JHNeronObjectAtP.LevelData p M H hpM A) (O' : JHNeronObjectAtP p M H hpM A hA Λ')
    (hD' : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O'.G, O'.g, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O'.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))
    (hΛ' : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ'.f) :
    ∃ e : JH M H ≃+ JH M H,
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H), e (σ • x) = σ • e x) ∧
      (∀ m : ℕ, 0 < m →
        (O'.toricPts m) = (O.toricPts m).map e.toAddMonoidHom ∧
        (O'.finPts m) = (O.finPts m).map e.toAddMonoidHom) := by sorry
