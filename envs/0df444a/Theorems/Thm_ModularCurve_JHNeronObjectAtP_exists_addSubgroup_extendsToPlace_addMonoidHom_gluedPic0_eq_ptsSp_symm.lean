-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
-- name    : ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/be12acf1-0e8e-588d-b53b-54b9df99c8ee
-- title:
--   Specialisation of A-integral points of a J_H(M) Néron object
-- statement:
--   Fix a prime $p$ and $M\neq 0$ with $p\mid M$, a subgroup $H\le(\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $A$ and with residue field algebraically closed of characteristic $p$. Let $\Lambda$ be level data for $(p,M,H,A)$, consisting of a morphism $\sigma_A\colon\operatorname{Spec} A\to \mathtt{base}\,p$ with $\mathtt{barPt}\,A$ followed by $\sigma_A$ equal to $\mathtt{genPt}\,p$, a scheme $X$ over $\mathtt{base}\,p$ with a relative group law and two identifications of its generic and special point sets, and let $O$ be a `JHNeronObjectAtP` for these data, with structure morphism $g\colon G\to\mathtt{base}\,p$, commutative relative group law $O.L$, generic point dictionary $O.\mathtt{pts}\colon J_H(M)\simeq\{\varphi : \varphi\circ g=\mathtt{genPt}\,p\}$ and special dictionary $O.\mathtt{ptsSp}$ identifying the glued degree-zero divisor class group $\mathrm{GluedPic}^0$ of the residue field with the set of points of $G$ over $\mathtt{resPt}\,A$ followed by $\sigma_A$. Here $J_H(M)$ is $\mathrm{Pic}^0$ of the function field $\mathtt{xHFunctionFieldBar}\,M\,H$, and $\mathrm{GluedPic}^0$ is the group of admissible gluing data modulo glued principal ones, over the gluing set $O.\mathtt{ssFinset}$. The assertion is the existence of an additive subgroup $\mathrm{dom}\le J_H(M)$ and an additive homomorphism $\mathrm{sp}\colon\mathrm{dom}\to\mathrm{GluedPic}^0$ such that: (i) $x\in\mathrm{dom}$ if and only if $O.\mathtt{pts}(x)$ extends to a point over $\sigma_A$, i.e. factors as $\mathtt{barPt}\,A$ followed by some $s$ with $s\circ g=\sigma_A$; (ii) for $x\in\mathrm{dom}$ and any such $s$, $\mathrm{sp}(x)=O.\mathtt{ptsSp}^{-1}$ of $\mathtt{resPt}\,A$ followed by $s$; (iii) $\mathrm{dom}$ is stable under the decomposition subgroup of $A$ over $\mathbb{Q}$; (iv) every $x\in\mathrm{dom}$ killed by some $n>0$ with $p\nmid n$ is fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$; (v) $\mathrm{sp}$ is injective on such prime-to-$p$ torsion; and (vi) every $\xi\in\mathrm{GluedPic}^0$ killed by some $n>0$ with $p\nmid n$ is $\mathrm{sp}(x)$ for some prime-to-$p$ torsion $x\in\mathrm{dom}$.
--
--   This packages the reduction (specialisation) map from the $A$-integral points of a Néron object for $J_H(M)$ at a place above $p$ to the generalised Jacobian of its glued special fibre, together with the standard properties: Galois equivariance of the domain, inertia-invariance and bijectivity on prime-to-$p$ torsion. It is the tool used downstream for the Tate module comparison, for identifying toric points, and for the Atkin–Lehner and Abel–Jacobi compatibilities at level $\Gamma_H(M)$ with $p\mid M$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  ModularCurve.JZeroNeronObjectAtP AlgebraicCurve
open scoped MatrixGroups

theorem ModularCurve.JHNeronObjectAtP.exists_addSubgroup_extendsToPlace_addMonoidHom_gluedPic0_eq_ptsSp_symm
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ) :
    ∃ (dom : AddSubgroup (JH M H))
      (sp : ↥dom →+ GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) O.ssFinset),

      (∀ x : JH M H, x ∈ dom ↔ ExtendsToPlace A Λ.σA (O.pts x)) ∧

      (∀ (x : ↥dom) (s : SchemeHomOver Λ.σA O.g), (O.pts (x : JH M H)).1 = barPt A ≫ s.1 →
        sp x = O.ptsSp.symm (GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s)) ∧

      (∀ σ ∈ A.decompositionSubgroup ℚ, ∀ x ∈ dom, σ • x ∈ dom) ∧

      (∀ x ∈ dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • x = 0) → ∀ σ ∈ A.inertiaSubgroupIn ℚ, σ • x = x) ∧

      (∀ x : ↥dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • (x : JH M H) = 0) → sp x = 0 → x = 0) ∧

      (∀ ξ : GluedPic0 (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) O.ssFinset,
        (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • ξ = 0) →
          ∃ x : ↥dom, (∃ n : ℕ, 0 < n ∧ ¬ p ∣ n ∧ n • (x : JH M H) = 0) ∧ sp x = ξ) := by sorry
