-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_schemeHomOverComp_torusFibre_degeneracyHom_eq_one
-- name    : ModularCurve.JHNeronObjectAtP.schemeHomOverComp_torusFibre_degeneracyHom_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/bdff7856-eee6-5491-819b-aac594b850f1
-- title:
--   Degeneracy homomorphisms kill the toric point of the special fibre
-- statement:
--   Fix a prime $p$ and $M \ge 1$ with $p \mid M$ and $p^2 \nmid M$ (so $M/p \ne 0$), and a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a non-unit of $A$, whose residue field $\kappa$ is algebraically closed of characteristic $p$. Let $\Lambda$ be level data at $A$ for $(p,M,H)$: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ extending the generic point, a scheme $X$ with structure morphism $\Lambda.f$ to $\operatorname{Spec} \mathbb{Z}_{(p)}$, a relative group law $\Lambda.L$ on it, and bijections identifying its points over the generic point with $J_H(M/p)$ for the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, and its points over $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}_{(p)}$ with $\mathrm{Pic}^0$ of the $q$-expansion function field of $\Gamma_N(p,M,H)$ over $\kappa$. Let $O$ be a level-$(M,H)$ Néron object over $\Lambda$, with toric rank $t = O.\mathrm{toricRank}$, toric point $O.\mathrm{torusFibre}$ of the special fibre of its structure morphism, indexed by the split torus $\operatorname{Spec}\kappa[\mathbb{Z}^t]$, and degeneracy morphisms $O.\mathrm{degeneracyHom}\,i$ to $X$ over $\operatorname{Spec}\mathbb{Z}_{(p)}$. Assume $\Lambda.f$ is smooth and proper with connected fibres and admits a relative group law, and that the special-fibre parametrisation $\Lambda.\mathrm{ptsSp}$ is additive, addition being taken in the group law obtained from $\Lambda.L$ by base change along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}_{(p)}$. Then for each $i \in \{0,1\}$ the toric point, pushed forward into the total space and then followed by $O.\mathrm{degeneracyHom}\,i$, equals the unit section of $\Lambda.L$ over $\operatorname{Spec}\kappa[\mathbb{Z}^t] \to \operatorname{Spec}\kappa \to \operatorname{Spec} A \to \operatorname{Spec}\mathbb{Z}_{(p)}$.
--
--   This is the scheme-theoretic form of the statement that the toric part of the special fibre at $p$ of the Jacobian at level $\Gamma_H(M)$, with $p \parallel M$, is annihilated by both degeneracy maps to the level-$M/p$ abelian scheme, the two rows of Ribet's matrix describing the fibre at $p$. It is used in the level-lowering argument at $p$, where it yields that the degree pairing vanishes on toric points, via [`ModularCurve.JHNeronObjectAtP.degPts_eq_zero_of_mem_toricPts`](thm.html#ModularCurve.JHNeronObjectAtP.degPts_eq_zero_of_mem_toricPts).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_schemeHomOverComp_torusFibre_degeneracyHom_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve
  IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.schemeHomOverComp_torusFibre_degeneracyHom_eq_one
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))
    (i : Fin 2) :
    NeronModelInfra.schemeHomOverComp (RelativeGroupLaw.baseChangePointToBase (resPt A ≫ Λ.σA) O.torusFibre) (O.degeneracyHom i) =
      Λ.L.one (torusStr (ResidueField ↥A) O.toricRank ≫ resPt A ≫ Λ.σA) := by sorry
