-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF
-- name    : ModularCurve.JZeroNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/2e854884-35e9-56a0-9354-98b498966ec4
-- title:
--   Special m-kernel of the J₀(N₀) datum has order m^{2g}
-- statement:
--   Fix a natural number $N_0 \ne 0$ and a prime $p$ with $p \nmid N_0$, a valuation subring $A$ of an algebraic closure of $\mathbf{Q}$ whose `LiesOverPrime p` holds, i.e. $p$ is a non-unit of $A$, and a level datum $\Lambda :$ `LevelData N₀ p A`: a morphism $\sigma_A : \operatorname{Spec} A \to$ `base p` lifting the generic point, a scheme $X$ with a morphism $f$ to `base p`, a relative group law $\Lambda.L$ on $f$ over `baseRing p`, and bijections of $J_0(N_0)$ with the sections of $f$ over the generic point and of `JZeroC` of the residue field $\kappa =$ `ResidueField A` at level $N_0$ with the sections over `resPt A ≫ Λ.σA`. Assume $\Lambda$ satisfies `IsJacobian`: $f$ carries an abelian-scheme property bundle over `baseRing p`, the group law is commutative, both point dictionaries are additive, the generic one is Galois-equivariant, reduction of points agrees mod $\ell$ when the relevant inputs hold, and the Hecke algebra acts by endomorphisms of $f$ compatible with the dictionary. Let $m > 0$. Then, writing $\mathcal{A}_\kappa$ for the base change of $\Lambda.L$ along `resPt A ≫ Λ.σA`, the structure morphism `schemeKerStr m` of the kernel of multiplication by $m$ (the pullback of `schemeNsmul m` along the unit section) is finite, and the global sections $\Gamma(\mathcal{A}_\kappa[m], \top)$, as a $\kappa$-algebra via that structure morphism, have $\kappa$-dimension $m^{2 g}$, where $g =$ `genusFF` $\kappa$ of `modularFunctionFieldC` $\kappa$ $N_0$, the subfield of $\kappa((q))$ generated over $\kappa$ by the $q$-expansions `jqModC` and `jqNModC`.
--
--   This computes the order of the $m$-torsion group scheme of the reduction of $J_0(N_0)$ at a place above a prime $p$ of good reduction, with no coprimality assumption on $m$ and $p$, so that for $p \mid m$ the kernel is non-reduced and the count is read off from the dimension of its coordinate ring rather than from a number of points. It feeds the finiteness of torsion subsets on the special fibre and the corresponding kernel count for the Néron object at $p$ of the level $N_0 p$ Jacobian.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open ModularCurve

theorem ModularCurve.JZeroNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_pow_two_mul_genusFF
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian) (m : ℕ) (hm : 0 < m) :
    IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ (2 * genusFF (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) := by sorry
