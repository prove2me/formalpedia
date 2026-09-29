-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_abqFibre_descent_zmodp
-- name    : ModularCurve.JHNeronObjectAtP.exists_abqFibre_descent_zmodp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/5e3d66b5-6d27-5baa-a9ce-a316ee2b3fb4
-- title:
--   Descent of the abelian-quotient fibre maps to 𝔽ₚ
-- statement:
--   Fix a prime $p$, a nonzero modulus $M$ with $p \mid M$, and a subgroup $H \le (\mathbb{Z}/M)^{\times}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa_A$ has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data for $p, M, H$ at $A$: a morphism $\Lambda.\sigma_A : \operatorname{Spec} A \to \mathtt{base}\,p = \operatorname{Spec}(\mathtt{baseRing}\,p)$ with $\mathtt{barPt}\,A \gg \Lambda.\sigma_A = \mathtt{genPt}\,p$, a scheme $\Lambda.X$ with structure morphism $\Lambda.f$ over $\mathtt{base}\,p$, a relative group law $\Lambda.L$ on $\Lambda.f$, and bijections of $J_H(M/p)$ for the induced subgroup with the sections of $\Lambda.f$ over $\mathtt{genPt}\,p$, and of $\mathrm{Pic}^0$ of the $\kappa_A$-function field at level $\Gamma$ with the sections over $\mathtt{resPt}\,A \gg \Lambda.\sigma_A$. Let $O$ be a Néron object for $J_H(M)$ over this level data, with structure morphism $O.g$, relative group law $O.L$ and the further data recorded in that structure, among them the two maps $O.\mathtt{abqFibre}\,i$ ($i \in \{0,1\}$), each a morphism over $\operatorname{Spec}\kappa_A$ from the base change of $O.g$ along $\mathtt{resPt}\,A \gg \Lambda.\sigma_A$ to the corresponding base change of $\Lambda.f$. Assume $\Lambda.f$ is separated and locally of finite type, that $\kappa_A$ is a $\mathbb{Z}/p$-algebra, and let $\sigma_p : \operatorname{Spec}(\mathbb{Z}/p) \to \mathtt{base}\,p$ be such that $\operatorname{Spec}$ of the structure map $\mathbb{Z}/p \to \kappa_A$ followed by $\sigma_p$ equals $\mathtt{resPt}\,A \gg \Lambda.\sigma_A$. The assertion is that there are morphisms $q_0, q_1$ from the base change of $O.g$ along $\sigma_p$ to the base change of $\Lambda.f$ along $\sigma_p$, each commuting with the projections to $\operatorname{Spec}(\mathbb{Z}/p)$, such that (i) each $q_i$ is a homomorphism for the base-changed group laws: for every scheme $T$ with $s : T \to \operatorname{Spec}(\mathbb{Z}/p)$ and all sections $x, y$ over $s$ of the base change of $O.g$, composing the $O.L$-base-change product of $x$ and $y$ with $q_i$ equals the $\Lambda.L$-base-change product of $x \gg q_i$ and $y \gg q_i$; and (ii) for each $i$, $O.\mathtt{abqFibre}\,i$ followed by the canonical map of pullbacks $\Lambda.X_{\kappa_A} \to \Lambda.X_{\mathbb{Z}/p}$ (identity on $\Lambda.X$, $\operatorname{Spec}$ of $\mathbb{Z}/p \to \kappa_A$ on the base) equals the analogous canonical map $O.G_{\kappa_A} \to O.G_{\mathbb{Z}/p}$ followed by $q_i$; that is, $q_i$ base-changes along $\operatorname{Spec}\kappa_A \to \operatorname{Spec}(\mathbb{Z}/p)$ to $O.\mathtt{abqFibre}\,i$.
--
--   This is a descent statement for morphisms: the two abelian-quotient maps of the special fibre of the Néron object, originally given only over the algebraically closed residue field $\kappa_A$, come by base change from maps defined over the prime field $\mathbb{F}_p$, compatibly with the relative group laws. It is used in the construction of the two-step tower with Raynaud quotient for the Néron object of $J_H(M)$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_abqFibre_descent_zmodp.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve
  ModularCurve.JZeroNeronObjectAtP

open ModularCurve in

theorem ModularCurve.JHNeronObjectAtP.exists_abqFibre_descent_zmodp
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)

    [IsSeparated Λ.f] [LocallyOfFiniteType Λ.f]

    [Algebra (ZMod p) (ResidueField ↥A)]
    (σp : Spec (CommRingCat.of (ZMod p)) ⟶ base p)
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A))) ≫ σp = resPt A ≫ Λ.σA) :
    ∃ q : Fin 2 → SchemeHomOver (RelativeGroupLaw.baseChangeStr σp O.g) (RelativeGroupLaw.baseChangeStr σp Λ.f),

      (∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of (ZMod p)))
        (x y : SchemeHomOver s (RelativeGroupLaw.baseChangeStr σp O.g)),
        NeronModelInfra.schemeHomOverComp ((O.L.baseChange σp).mul s x y) (q i) =
          (Λ.L.baseChange σp).mul s (NeronModelInfra.schemeHomOverComp x (q i)) (NeronModelInfra.schemeHomOverComp y (q i))) ∧

      (∀ i : Fin 2,
        (O.abqFibre i).1 ≫ pullback.map Λ.f (resPt A ≫ Λ.σA) Λ.f σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) =
          pullback.map O.g (resPt A ≫ Λ.σA) O.g σp (𝟙 _)
            (Spec.map (CommRingCat.ofHom (algebraMap (ZMod p) (ResidueField ↥A)))) (𝟙 _)
            (by rw [Category.comp_id, Category.id_comp]) (by rw [Category.comp_id]; exact hfac.symm) ≫ (q i).1) := by sorry
