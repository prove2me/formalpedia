-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre
-- name    : ModularCurve.JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/6622ea75-84c9-59df-8847-54af839beb1a
-- title:
--   Special-fibre torus as joint kernel of the abelian-quotient pair
-- statement:
--   Fix a prime $p$, a nonzero $M$ with $p \mid M$, a subgroup $H \le (\mathbf Z/M)^\times$, and a valuation subring $A$ of $\overline{\mathbf Q}$ lying over $p$ in the sense that the image of $p$ in $A$ is a non-unit, whose residue field $\kappa =$ `ResidueField ↥A` has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data at $p$ for $(M,H)$: a morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` lifting the generic point, a scheme $X$ with $f : X \to$ `base p`, a relative group law $\Lambda.L$ on $f$ over `baseRing p`, and dictionaries identifying the generic-fibre points with $J_H(M/p)$ at the induced level and the $\kappa$-points with the degree-zero divisor class group of the reduced curve; assume $f$ proper. Let $O$ be a `JHNeronObjectAtP` for these data, with toric rank $t = O.\mathrm{toricRank}$, torus map $O.\mathrm{torusFibre}$, and abelian-quotient pair $O.\mathrm{abqFibre}$, a pair of morphisms from the $\kappa$-fibre of $O$ to that of $\Lambda$, each compatible with multiplication by $O.\mathrm{abqFibre\_mul}$. Then there is an isomorphism of schemes $e$ from the split torus $\operatorname{Spec} \kappa[(\mathbf Z^t)]$ onto the joint kernel `kerPair` of $O.\mathrm{abqFibre}$ for the base change of $\Lambda.L$ along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to$ `base p` (the fibre product of the preimages of the two unit sections) such that $e$ followed by the inclusion of the joint kernel equals $O.\mathrm{torusFibre}$, and such that for every $n \in \mathbf N$, $e$ followed by the $n$-fold multiplication morphism of the group law induced on the joint kernel by the base change of $O.L$ equals the endomorphism $\operatorname{Spec}$ of multiplication by $n$ on the character lattice $\mathbf Z^t$, followed by $e$.
--
--   This identifies the toric part of the special fibre of the Néron object attached to $J_H(M)$ at $p$ with the subgroup scheme of points killed by both abelian-quotient maps, compatibly with the $n$-th power maps; it is the scheme-theoretic form of the toric exact sequence for the reduction of the Jacobian at a prime dividing the level exactly once. It is used in the subsequent analysis of the $p$-torsion of the special fibre: the construction of fppf-local sections of the kernel scheme, the bound on the $\kappa$-dimension of the relevant quotient by $p^{t}$, and the finiteness and degree computation for the special kernel scheme.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_iso_torus_kerPair_abqFibre.lean

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

theorem ModularCurve.JHNeronObjectAtP.exists_iso_torus_kerPair_abqFibre
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (hΛ : IsProper Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    ∃ e : torusScheme (ResidueField ↥A) O.toricRank ≅
        RelativeGroupLaw.kerPair (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre,
      e.hom ≫ RelativeGroupLaw.kerPairι (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre = O.torusFibre.1 ∧
      ∀ n : ℕ, e.hom ≫ (RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
          (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)).schemeNsmul n =
        Spec.map (CommRingCat.ofHom
          (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) (n • AddMonoidHom.id (Fin O.toricRank → ℤ)))) ≫
          e.hom := by sorry
