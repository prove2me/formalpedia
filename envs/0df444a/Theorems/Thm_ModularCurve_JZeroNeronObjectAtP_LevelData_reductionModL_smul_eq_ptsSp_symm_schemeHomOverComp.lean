-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_reductionModL_smul_eq_ptsSp_symm_schemeHomOverComp
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelData.reductionModL_smul_eq_ptsSp_symm_schemeHomOverComp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e0b86ff2-fd5a-52e7-ba80-d604276d170f
-- title:
--   Reduction mod p intertwines Hecke action on the special fibre
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0\neq 0$, $p$ prime and nonzero, and $p\nmid N_0$; let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A$. Let $\Lambda$ be a level datum `LevelData N₀ p A`: a structure morphism $\sigma_A\colon\operatorname{Spec}A\to$ `base p` compatible with the generic point, a scheme $\Lambda.X$ with a morphism $f\colon\Lambda.X\to$ `base p`, a relative group law on $f$, and bijections $\Lambda.\mathrm{pts}$ from `JZero N₀` $=\mathrm{Pic}^0$ of the level-$N_0$ modular function field over $\overline{\mathbb Q}$ to the sections of $f$ over the generic point, and $\Lambda.\mathrm{ptsSp}$ from `JZeroC (ResidueField A) N₀` to the sections of $f$ over `resPt A ≫ σA`. Assume $\Lambda.\mathrm{IsJacobian}$, i.e. the conjunction of the abelian-scheme property bundle for $f$, commutativity of the group law, additivity and Galois-equivariance of $\Lambda.\mathrm{pts}$, additivity of $\Lambda.\mathrm{ptsSp}$, the reduction-compatibility conjunct (valid whenever `ReductionInputsModL A N₀` holds), and the existence, for each Hecke element, of an endomorphism of $f$ inducing it. Let $t\in$ `HeckeAlg` $=\mathbb Z[x_\ell:\ell\text{ prime}]$, and let $\varphi'$ be an endomorphism of $\Lambda.X$ over `base p` such that, for the module structure `heckeModuleBar N₀`, the section $\Lambda.\mathrm{pts}(t\cdot x)$ is $\Lambda.\mathrm{pts}(x)$ followed by $\varphi'$ for every $x$. Then for every $y$ in `JZero N₀`, the reduction $\mathrm{red}_A(t\cdot y)$ equals $\Lambda.\mathrm{ptsSp}^{-1}$ applied to the section $\Lambda.\mathrm{ptsSp}(\mathrm{red}_A(y))$ followed by $\varphi'$, where $\mathrm{red}_A=$ `reductionModL A N₀` is reduction of divisor classes along the residue map of $A$.
--
--   This is the classical compatibility, going back to Deuring and Shimura, between reduction of divisor classes at a prime of good reduction and the Hecke action: reduction intertwines the level-$N_0$ Hecke operator with the operator transported to the special fibre by the endomorphism $\varphi'$ of the Néron/abelian-scheme model. It is the source of Hecke-equivariance statements on the special fibre used later, for instance in the results producing lower-level torsion and showing that Hecke torsion subgroups are nonzero.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_reductionModL_smul_eq_ptsSp_symm_schemeHomOverComp.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open ModularCurve

theorem ModularCurve.JZeroNeronObjectAtP.LevelData.reductionModL_smul_eq_ptsSp_symm_schemeHomOverComp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (t : HeckeAlg) (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (t • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (y : JZero N₀) :
    letI := heckeModuleBar N₀
    reductionModL A N₀ (t • y) = Λ.ptsSp.symm (NeronModelInfra.schemeHomOverComp (Λ.ptsSp (reductionModL A N₀ y)) φ') := by sorry
