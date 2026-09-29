-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
-- name    : ModularCurve.JHNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/59f08873-9b4c-5917-89b3-fa13b3cf960b
-- title:
--   Frobenius and Uₚ torus matrices are mutually inverse
-- statement:
--   Fix a prime $p$ and a modulus $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ whose residue field $\kappa = \mathrm{ResidueField}\,A$ has characteristic $p$ and is algebraically closed; fix level data $\Lambda$ (in particular a section $\Lambda.\sigma_A$ of the base over $A$) and a Néron object $O$ for $J_H(M)$ at $p$ over these data, with toric rank $r = O.\mathrm{toricRank}$ and its finite set $O.\mathrm{ssFinset}$ of pairs of places of the $q$-expansion function field $\mathrm{Fbar}$ over $\kappa$. The data are: an endomorphism $\Xi_G$ of the special fibre $\mathrm{pullback}\,O.g\,(\mathrm{resPt}\,A \gg \Lambda.\sigma_A)$ commuting with the first projection and inducing the $p$-power Frobenius of $\kappa$ on the second projection; an additive endomorphism $P_0$ of $\mathbb{Z}^r$ such that the coefficientwise Frobenius on $\kappa[\mathbb{Z}^r]$ followed by the toric chart $O.\mathrm{torusFibre}$ equals the map induced by $P_0$ on the group $\mathbb{Z}^r$ followed by the toric chart followed by $\Xi_G$; a set $S \subseteq \mathbb{N}$ and an additive endomorphism $M_0$ of $\mathbb{Z}^r$ such that the map induced by $M_0$ followed by the toric chart equals the toric chart followed by the restriction to the special fibre of the Hecke endomorphism $O.\mathrm{hecke}\,S\,(U_p)$. Two hypotheses in node coordinates are assumed: first, for every permutation $\mathrm{perm}$ of $O.\mathrm{ssFinset}$ sending each node componentwise to its image under $\mathrm{qExpFrobeniusPlaceModL}$, every automorphism $\varphi$ of $\overline{\mathbb{Q}}$ in the decomposition subgroup of $A$ acting as $x \mapsto x^p$ on $\kappa$, every $x \in J_H(M)$, and all $A$-sections $s, s'$ of $O.g$ over $\Lambda.\sigma_A$ lifting the points $x$ and $\varphi \cdot x$ after base change along $\mathrm{barPt}\,A$: if the special point of $s$ is the node-unit class of $w : O.\mathrm{ssFinset} \to \mathrm{Additive}\,\kappa^\times$, then that of $s'$ is the node-unit class of $t \mapsto p \cdot w(\mathrm{perm}^{-1}t)$; second, there is a permutation $\sigma_N$ of $O.\mathrm{ssFinset}$ whose second component at $n$ is the first component of $n$, such that composing the section attached to the node-unit class of $w$ with $O.\mathrm{hecke}\,S\,(U_p)$ gives the node-unit class of $w \circ \sigma_N$. Finally an automorphism $\varphi$ of $\overline{\mathbb{Q}}$ in the decomposition subgroup of $A$ inducing $x \mapsto x^p$ on $\kappa$ is given. The conclusion is that $P_0 \circ M_0$ and $M_0 \circ P_0$ are both the identity of $\mathbb{Z}^r$.
--
--   On the toric part of the special fibre at $p$ of the Jacobian of $X_H(M)$, the Hecke operator $U_p$ and the Frobenius act on the character lattice $\mathbb{Z}^r$ by mutually inverse integer matrices; the argument is the cancellation of the Frobenius permutation of the nodes against the node shift $\sigma_N$ induced by $U_p$, transported from node coordinates to integer matrices. It is used in the computation of the $U_p$-action on toric points and in the identification, via the cyclotomic character, of the Tate-module avatar of $U_p$ at a Frobenius element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_frobMatrix_comp_torusMatrix_eq_id_of_hecke_U.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.frobMatrix_comp_torusMatrix_eq_id_of_hecke_U
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)

    (ΞG : pullback O.g (resPt A ≫ Λ.σA) ⟶ pullback O.g (resPt A ≫ Λ.σA))
    (hΞ₁ : ΞG ≫ pullback.fst _ _ = pullback.fst _ _)
    (hΞ₂ : ΞG ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (frobenius (ResidueField ↥A) p)))

    (P₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hP₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (Fin O.toricRank → ℤ) (frobenius (ResidueField ↥A) p))) ≫ O.torusFibre.1 =
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) P₀)) ≫ O.torusFibre.1 ≫ ΞG)

    (S : Set ℕ)
    (M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ))
    (hM₀ : Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
      O.torusFibre.1 ≫ (NeronSpecialFibreInfra.fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g (O.hecke S (CohCarrier.Gen.U p (Fact.out) hpM))).1)

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
    P₀.comp M₀ = AddMonoidHom.id _ ∧ M₀.comp P₀ = AddMonoidHom.id _ := by sorry
