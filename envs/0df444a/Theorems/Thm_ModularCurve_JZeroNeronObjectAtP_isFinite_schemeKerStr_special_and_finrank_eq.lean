-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq
-- name    : ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/8c4f1aaa-43d2-596d-9343-9e4ba0510a74
-- title:
--   Order of the special m-kernel: m^{t+4g₀}
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0$ and $p$ nonzero, $p$ prime and $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbf{Q}}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A$; write $\kappa = \mathrm{ResidueField}\ A$. Let $\Lambda$ be a level-$N_0$ datum at $p$ over $A$ — a scheme $X$ over `base p` with a relative group law $\Lambda.L$, a section $\sigma_A$ over $A$ whose restriction to the generic point is `genPt p`, and bijections of $J_0(N_0)$-groups with the generic and special points of $X$ — subject to the Jacobian hypotheses $h\Lambda$ (abelian-scheme bundle, commutativity, additivity and Galois equivariance of the point parametrisations, compatibility of reduction mod $\ell$, and Hecke equivariance; summarised here). Let $O$ be a Néron object of level $N_0p$ over this datum, with relative group law $O.L$, toric rank $O.\mathrm{toricRank}$, and the smoothness, separatedness, finite type, quasi-compactness, surjectivity, connected-fibre, flat and surjective multiplication-by-$n$, and properness-of-generic-fibre data recorded in the structure. Then for every $m > 0$: the structure morphism to $\operatorname{Spec}\kappa$ of the $m$-kernel of the base change of $O.L$ along $\kappa$-point `resPt A ≫ Λ.σA` — the pullback of multiplication by $m$ along the unit section — is a finite morphism, and the ring of global sections of that kernel, as a $\kappa$-algebra via this structure morphism, has $\kappa$-dimension $m^{\,O.\mathrm{toricRank} + 4g_0}$, where $g_0 = \mathrm{genusFF}$ of the level-$N_0$ modular function field $\kappa(j_q, j_{q,N_0}) \subset \kappa((q))$ over $\kappa$, i.e. the $\kappa$-dimension of $H^1$ of the zero divisor.
--
--   This computes the order of the $m$-torsion of the special fibre of the identity component of the Néron model of $J_0(N_0p)$ at $p$, valid also when $p \mid m$, where the torsion is not seen on $\kappa$-points. It feeds the counting of points of the special fibre ([`ModularCurve.JZeroNeronObjectAtP.natCard_finPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.natCard_finPts)) and the package of properties of the special $m$-kernel ([`ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props`](thm.html#ModularCurve.JZeroNeronObjectAtP.schemeKerStr_baseChange_props)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve
  IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m) :
    IsFinite ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ (O.toricRank + 4 * genusFF (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) := by sorry
