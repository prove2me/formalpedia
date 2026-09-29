-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/3c39a54d-139c-54d7-82aa-972e3324f34f
-- title:
--   fppf-local sections of the m-torsion comparison map
-- statement:
--   Let $N_0$ and $p$ be natural numbers with $N_0 \neq 0$ and $p$ prime, and suppose $p \nmid N_0$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ lying in the non-units of $A$, let $\Lambda$ be a level datum of type `LevelData N₀ p A` (a structure map $\sigma_A \colon \operatorname{Spec} A \to$ `base p` restricting to the generic point, a scheme $X$ over `base p` with relative group law $\Lambda.L$, and parametrisations of the points of $J_0$ and of its reduction), assume $\Lambda$ satisfies `IsJacobian`, and let $O$ be an object of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with relative group law $O.L$. Write $\kappa$ for the residue field of $A$ and base change both group laws along $\operatorname{Spec}\kappa \to \operatorname{Spec} A \to$ `base p`. Let $m > 0$ and let $\psi$ be a morphism from the $m$-torsion scheme of $O.L_\kappa$, that is the pullback of the $m$-fold sum map `schemeNsmul m` along the unit section, to the fibre product over $\kappa$ of two copies of the corresponding $m$-torsion scheme of $\Lambda.L_\kappa$; assume that $\psi$ followed by the first (respectively second) projection and then by the inclusion into the $\Lambda$-side scheme equals the inclusion of the $O$-side $m$-torsion followed by the underlying morphism of `O.abqFibre 0` (respectively `O.abqFibre 1`). Then there exist a scheme $U$, a morphism $u \colon U \to \Lambda_\kappa[m] \times_\kappa \Lambda_\kappa[m]$ that is flat, surjective and locally of finite presentation, and a morphism $s \colon U \to O_\kappa[m]$ with $s$ followed by $\psi$ equal to $u$.
--
--   The assertion is that the comparison morphism $\psi$ from the $m$-torsion of the special fibre of the Néron-type object to the square of the $m$-torsion of the Jacobian side admits sections after a faithfully flat, locally finitely presented cover, i.e. fppf-locally. It is used in the computation of the degree and finiteness of the $m$-torsion on the special fibre, via the Kummer-type statement for split tori and the identification of the kernel pair of `abqFibre` with a split torus of rank `O.toricRank`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_fppfCover_section_schemeKer_of_abqFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_fppfCover_section_schemeKer_of_abqFibre
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
    (ψ : (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m ⟶
      pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
    (hψ₀ : ψ ≫ pullback.fst _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 0).1)
    (hψ₁ : ψ ≫ pullback.snd _ _ ≫ pullback.fst ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 =
      pullback.fst ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeNsmul m) ((O.L.baseChange (resPt A ≫ Λ.σA)).one (𝟙 _)).1 ≫
        (O.abqFibre 1).1) :
    ∃ (U : Scheme.{0}) (u : U ⟶ pullback ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m)
        ((Λ.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m))
      (_ : Flat u) (_ : Surjective u) (_ : LocallyOfFinitePresentation u)
      (s : U ⟶ (O.L.baseChange (resPt A ≫ Λ.σA)).schemeKer m), s ≫ ψ = u := by sorry
