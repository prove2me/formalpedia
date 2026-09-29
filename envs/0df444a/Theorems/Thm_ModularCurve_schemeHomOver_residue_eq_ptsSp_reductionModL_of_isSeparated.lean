-- Prove2me | Theorems.Thm_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
-- name    : ModularCurve.schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/23044979-bd8e-5865-a190-8c9c9c737710
-- title:
--   Separatedness pins the reduction of a B-point
-- statement:
--   Fix a prime $p$, a valuation subring $B$ of $\overline{\mathbb{Q}}$, a commutative ring $R$, a scheme $J$ and a morphism $f : J \to \operatorname{Spec} R$ which is separated, together with a morphism $\sigma_B : \operatorname{Spec} B \to \operatorname{Spec} R$. Assume given two bijections: `ptsA`, from $\mathrm{JZero}\,p = \mathrm{Pic}^0$ of the level-$p$ modular function field base-changed to $\overline{\mathbb{Q}}$ (degree-zero divisors modulo principal ones) to the set of morphisms $\operatorname{Spec}\overline{\mathbb{Q}} \to J$ whose composite with $f$ is $\sigma_B \circ \operatorname{Spec}(B \hookrightarrow \overline{\mathbb{Q}})$; and `ptsSp`, from $\mathrm{JZeroC}$ of the residue field of $B$ at level $p$ to the morphisms $\operatorname{Spec}(B/\mathfrak{m}_B) \to J$ whose composite with $f$ is $\sigma_B \circ \operatorname{Spec}(\text{residue map})$. Assume further `ReductionOfPointsAgreesModL`: for every $x$ in $\mathrm{JZero}\,p$ there is a morphism $x_B : \operatorname{Spec} B \to J$ over $\sigma_B$ whose restriction along $B \hookrightarrow \overline{\mathbb{Q}}$ is `ptsA x` and whose restriction along the residue map is $\mathrm{ptsSp}(\mathrm{reductionModL}\,B\,p\,x)$, where $\mathrm{reductionModL}$ is the reduction homomorphism `reductionAlong B (residue B) p`. Then for any $x$ and any morphism $P : \operatorname{Spec} B \to J$ with $P \circ f$-composite equal to $\sigma_B$ whose restriction to $\operatorname{Spec}\overline{\mathbb{Q}}$ equals `ptsA x`, the restriction of $P$ to $\operatorname{Spec}(B/\mathfrak{m}_B)$ equals $\mathrm{ptsSp}(\mathrm{reductionModL}\,B\,p\,x)$.
--
--   This is the uniqueness half of the valuative criterion of separatedness, in the form needed for the Jacobian of the modular curve: a $B$-valued point of the model is determined by its generic fibre, so its special fibre is forced to be the reduction mod $\mathfrak{m}_B$ of the corresponding divisor class. It is used in the study of the identity component and primary torsion of the Néron model of $J_0(p)$, notably by [`ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL`](thm.html#ModularCurve.JZeroNeronIdentityComponentGood.exists_jZeroNeronPrimaryTorsionCore_two_residue_iff_reductionModL).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated.lean

import Definitions.Def_ModularCurve_JZeroNeronTorsionSheafV4
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve AlgebraicGeometry AlgebraicGeometry.Scheme
open CategoryTheory NeronModelInfra IsLocalRing

theorem ModularCurve.schemeHomOver_residue_eq_ptsSp_reductionModL_of_isSeparated
    (p : ℕ) [Fact p.Prime]
    (B : ValuationSubring (AlgebraicClosure ℚ))
    {R : Type} [CommRing R]
    (J : Scheme.{0}) (f : J ⟶ Spec (CommRingCat.of R))
    (hsep : IsSeparated f)
    (σB : Spec (CommRingCat.of ↥B) ⟶ Spec (CommRingCat.of R))
    (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom B.subtype) ≫ σB) f)
    (ptsSp : JZeroC (ResidueField ↥B) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ σB) f)
    (hROPAML : ReductionOfPointsAgreesModL p B f σB ptsA ptsSp)
    (x : JZero p) (P : SchemeHomOver σB f)
    (hgen : Spec.map (CommRingCat.ofHom B.subtype) ≫ P.1 = (ptsA x).1) :
    Spec.map (CommRingCat.ofHom (residue ↥B)) ≫ P.1
      = (ptsSp (reductionModL B p x)).1 := by sorry
