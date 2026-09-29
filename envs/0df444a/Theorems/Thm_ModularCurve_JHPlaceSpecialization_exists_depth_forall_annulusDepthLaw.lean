-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_depth_forall_annulusDepthLaw
-- name    : ModularCurve.JHPlaceSpecialization.exists_depth_forall_annulusDepthLaw
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/c101d5b9-0269-53bf-b929-acbae8b13682
-- title:
--   A depth function obeying the annulus depth law at every node
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ and $M/p$ non-zero, let $H \le (\mathbb{Z}/M)^\times$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ for which $p$ is a non-unit of $A$ and whose residue field $\kappa$ has characteristic $p$ and is algebraically closed. Write $F_M$ for the base change to $\overline{\mathbb{Q}}$ of the Laurent-series function field $X_H(M)$, $F_{M/p}$ for the corresponding field at level $(M/p, \mathrm{infSubgroup}\,p\,M\,H)$, and $\bar F$ for the $\kappa$-field `JHNeronObjectAtP.Fbar`. Let $P$ be a `JHPlaceSpecialization` for these data (a specialisation map $\mathrm{sp}$ from places of $F_{M/p}$ to places of $\bar F$ together with a map on degree-zero Picard groups and the compatibilities recorded in that structure), and let $\alpha : F_{M/p} \to F_M$ be an integral $\overline{\mathbb{Q}}$-algebra map, so that $P.\mathrm{reduceFst}\,\alpha$ sends a place $V$ of $F_M$ to $\mathrm{sp}$ of its restriction along $\alpha$. Let $SS$ be a finite set of pairs of places of $\bar F$ over $\kappa$ whose first coordinates are pairwise distinct (any two members of $SS$ with equal first coordinate are equal), and for each $s \in SS$ let $\mathrm{An}\,s$ be an `Annulus` for $A$ in $F_M$, that is a domain of places, a parameter $\mathrm{param} \in F_M$ and a modulus in the maximal ideal of $A$ satisfying the axioms of that structure. Assume each parameter $(\mathrm{An}\,s).\mathrm{param}$ is fixed by every element of the inertia subgroup of $A$ over $\mathbb{Q}$ acting through `arithmeticGalois` for $X_H(M)$, and assume that every place $V$ of $F_M$ with $P.\mathrm{reduceFst}\,\alpha\,V = s.1.1$ which is fixed by that inertia action lies in $(\mathrm{An}\,s).\mathrm{dom}$. Then there is a single function $\mathrm{depth}$ from places of $F_M$ to $\mathbb{N}$ such that: for each $s \in SS$ the pair $(\mathrm{An}\,s, \mathrm{depth})$ satisfies `AnnulusDepthLaw` for $P$, $\alpha$ and $s$, i.e. $v_A(V.\mathrm{evalAt}\,(\mathrm{An}\,s).\mathrm{param}) = v_A(p)^{\mathrm{depth}(V)}$ for every inertia-fixed $V$ with $P.\mathrm{reduceFst}\,\alpha\,V = s.1.1$; for every such $s$ and $V$ one has $1 \le \mathrm{depth}(V)$ and $v_A((\mathrm{An}\,s).\mathrm{modulus}) < v_A(p)^{\mathrm{depth}(V)}$; and $\mathrm{depth}(V) = 0$ whenever $P.\mathrm{reduceFst}\,\alpha\,V$ differs from the first coordinate of every member of $SS$.
--
--   This packages the integrality of the depth of inertia-fixed places on an annulus into one global depth function on the places of $X_H(M)$, indexed by a finite family of node data in the special fibre at $p$. It is the depth weight used in the depth–component description of the Néron model of $J_H(M)$ at $p$, and feeds into the assembly of the degeneracy, depth and surjectivity laws for `JHPlaceSpecialization`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_depth_forall_annulusDepthLaw.lean

import Definitions.Def_ModularCurve_JHNodeDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.JHPlaceSpecialization.exists_depth_forall_annulusDepthLaw
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (P : JHPlaceSpecialization p M H hpM A)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s ∈ SS, ∀ s' ∈ SS, s.1 = s'.1 → s = s')
    (An : ↥SS → AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hz : ∀ (s : ↥SS), ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • (An s).param = (An s).param)
    (hdom : ∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      P.reduceFst α hα V = s.1.1 →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
      V ∈ (An s).dom) :
    ∃ depth : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) → ℕ,
      (∀ s : ↥SS, P.AnnulusDepthLaw α hα (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (An s) depth) ∧
      (∀ (s : ↥SS) (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
        P.reduceFst α hα V = s.1.1 →
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • V = V) →
        1 ≤ depth V ∧
          A.valuation (((An s).modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation ((p : ℕ) : AlgebraicClosure ℚ) ^ depth V) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∀ s : ↥SS, P.reduceFst α hα V ≠ s.1.1) → depth V = 0) := by sorry
