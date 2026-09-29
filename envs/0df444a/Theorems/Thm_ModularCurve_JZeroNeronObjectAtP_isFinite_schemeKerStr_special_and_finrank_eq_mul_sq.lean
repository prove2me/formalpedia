-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
-- name    : ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/8eb6410e-1b24-5a95-a567-6121504f37dd
-- title:
--   Order of the special m-kernel: m^t times a square
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0$ and $p$ nonzero, $p$ prime, and $p \nmid N_0$, and let $A$ be a valuation subring of a fixed algebraic closure of $\mathbf{Q}$ lying over $p$, in the sense that the image of $p$ lies in the nonunits of $A$; write $\kappa =$ `ResidueField ↥A`. Let $\Lambda$ be a level datum of level $N_0$ at $p$ for $A$ — a structure morphism $\Lambda.\sigma_A \colon \operatorname{Spec} A \to$ `base p` over the generic point, a scheme $\Lambda.X$ over `base p` with a relative group law $\Lambda.L$, and bijections between `JZero N₀` (resp. its residue-field analogue) and the sections over the generic (resp. residual) point — and assume $\Lambda$ satisfies `IsJacobian`: the abelian-scheme property bundle, commutativity of $\Lambda.L$, additivity and Galois equivariance of the generic parametrisation, additivity of the residual parametrisation, agreement of reduction of points mod $\ell$ when the relevant inputs hold, and realisation of the Hecke algebra by endomorphisms. Let $O$ be a Néron object at $p$ of level $N_0p$ over these data, with group law $O.L$ and toric rank $O.\mathrm{toricRank}$, and let $m > 0$. Assume that for the base change of $\Lambda.L$ along `resPt A ≫ Λ.σA` (the special fibre over $\kappa$) the $m$-kernel structure morphism — the second projection of the pullback of the $m$-fold multiplication morphism along the identity section — is a finite morphism. The conclusion is twofold: the corresponding $m$-kernel structure morphism for the base change of $O.L$ along `resPt A ≫ Λ.σA` is also finite, and, with the $\kappa$-algebra structures on global sections induced by these structure morphisms, $$\dim_\kappa \Gamma\bigl((O.L\text{-base change})\text{'s } m\text{-kernel}, \top\bigr) = m^{O.\mathrm{toricRank}} \cdot \Bigl(\dim_\kappa \Gamma\bigl((\Lambda.L\text{-base change})\text{'s } m\text{-kernel}, \top\bigr)\Bigr)^{2}.$$
--
--   This is the scheme-theoretic dévissage of the special fibre of the Néron model of $J_0(N_0p)$ at $p$: the special fibre is an extension of two copies of the abelian part by a split torus of rank equal to the toric rank, so that the orders of the $m$-kernels multiply, the toric contribution being $m^{t}$ coming from $\mu_m^{t}$. It feeds the unconditional finiteness-and-order statement [`ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq`](thm.html#ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq), which in turn supports the local analysis at $p$ of the mod-$\ell$ representations attached to $J_0(N_0p)$ in Ribet's level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq.lean

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

theorem ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (hB : IsFinite ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)) :
    IsFinite ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ∧
    (letI := Scheme.TwoAffineOpenCover.algebraOfHom ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     letI := Scheme.TwoAffineOpenCover.algebraOfHom ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ⊤
     Module.finrank (ResidueField ↥A) Γ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) =
       m ^ O.toricRank *
         Module.finrank (ResidueField ↥A) Γ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m, ⊤) ^ 2) := by sorry
