-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre
-- name    : ModularCurve.JHNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/3c1bc7c7-d6bc-560c-b6d0-bec372f9d80c
-- title:
--   Shear isomorphism for m-torsion over the abelian-quotient kernel
-- statement:
--   Fix a prime $p$, a non-zero modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and with residue field $\kappa =$ `ResidueField ↥A` algebraically closed of characteristic $p$. Let $\Lambda$ be level data at $p$ for $(M,H)$ over $A$ — a structure morphism $\Lambda.\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec}(\mathrm{baseRing}\,p)$ lifting the generic point, a scheme $\Lambda.X$ with morphism $\Lambda.f$ to the base, a relative group law $\Lambda.L$ on it, and point dictionaries at the generic and residual points — with $\Lambda.f$ proper, and let $O$ be a level-$\Gamma_H(M)$ Néron object at $p$ over $\Lambda$. Write $\iota =$ `resPt A ≫ Λ.σA` $\colon \operatorname{Spec}\kappa \to$ base, and base change both group laws along $\iota$. Let $m > 0$ and let $\psi$ be a morphism from the $m$-torsion scheme $\operatorname{pullback}$ of the $m$-fold multiplication map of $O.L$ base changed and its unit section, to the fibre product over $\operatorname{Spec}\kappa$ of two copies of the corresponding $m$-torsion of $\Lambda.L$ base changed, such that composing $\psi$ with each projection and then with the inclusion of $\Lambda$'s $m$-torsion agrees with the inclusion of $O$'s $m$-torsion followed by `(O.abqFibre 0).1`, respectively `(O.abqFibre 1).1`. Let `KL` be the relative group law `kerPairLaw` on the joint kernel of the pair `O.abqFibre` inside the base-changed special fibre of $O$, built using the multiplicativity statements `O.abqFibre_mul`. The assertion is that there exists an isomorphism $\varphi$ between the fibre product over $\operatorname{Spec}\kappa$ of the $m$-torsion of `KL` with the $m$-torsion of $O.L$ base changed, and the fibre product of $\psi$ with itself, such that $\varphi$ followed by the second projection of $\operatorname{pullback} \psi\,\psi$ equals the second projection of the first fibre product.
--
--   This is the pseudo-torsor half of the assertion that the $m$-torsion of the special fibre of the level-$\Gamma_H(M)$ Néron object is a torsor under the $m$-torsion of the joint kernel of the two abelian-quotient maps, relatively over the $m$-torsion of the level-$(M/p)$ object: the shear map $(k,x) \mapsto (kx, x)$ is an isomorphism onto the fibre product of $\psi$ with itself. It feeds the finiteness and rank computation [`ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq`](thm.html#ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq) for the torsion of the special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair
import Definitions.Def_AlgebraicGeometry_SplitTorusMu
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP AlgebraicCurve
open scoped TensorProduct

theorem ModularCurve.JHNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶
      pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
    (hψ₀ : ψ ≫ pullback.fst _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 0).1)
    (hψ₁ : ψ ≫ pullback.snd _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 1).1) :
    letI KL := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
      (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)
    ∃ φ : pullback (KL.schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ≅ pullback ψ ψ,
      φ.hom ≫ pullback.snd ψ ψ = pullback.snd _ _ := by sorry
