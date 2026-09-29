-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/7ece4231-54dc-5552-9f9e-3d9a0b26df78
-- title:
--   Shear isomorphism for m-torsion over the abelian-quotient kernel pair
-- statement:
--   Fix naturals $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, a level datum $\Lambda$ of level $N_0$ at $p$ over $A$ satisfying `Λ.IsJacobian`, and an object $O$ of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`. Let $m > 0$, and write $\kappa$ for the residue field of $A$, so that base change along `resPt A ≫ Λ.σA` turns the relative group laws `O.L` and `Λ.L` into relative group laws over $\kappa$; for such a law, $\mathrm{schemeKer}\,m$ is the fibre product of multiplication by $m$ with the identity section, with structure morphism $\mathrm{schemeKerStr}\,m$ to $\operatorname{Spec}\kappa$. Let $\psi$ be a morphism from the $m$-torsion of the base-changed `O.L` to the fibre product of two copies of the $m$-torsion of the base-changed `Λ.L`, whose two components are, after composing with the canonical maps of $m$-torsion schemes into the ambient schemes, the restrictions of the two morphisms `O.abqFibre 0` and `O.abqFibre 1` (hypotheses $h\psi_0$, $h\psi_1$). Let $KL$ be the kernel-pair group law `kerPairLaw` attached to the base-changed laws, the pair `O.abqFibre` and the properties `O.abqFibre_mul`. Then there is an isomorphism of schemes from the fibre product over $\operatorname{Spec}\kappa$ of the $m$-torsion of $KL$ with the $m$-torsion of the base-changed `O.L` onto the fibre product of $\psi$ with itself, commuting with the projections to the second factor.
--
--   This is the pseudo-torsor (shear-map) half of the assertion that the $m$-torsion of the special fibre is a torsor under the $m$-torsion of the kernel of the abelian-quotient pair over the $m$-torsion of the abelian quotient. It is used in the computation of the finiteness and rank of the $m$-torsion of the special fibre, in [`ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq`](thm.html#ModularCurve.JZeroNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_iso_pullback_schemeKer_torus_of_abqFibre.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKerPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
  ModularCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_iso_pullback_schemeKer_torus_of_abqFibre
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
    letI KL := GoodReductionJacobian.RelativeGroupLaw.kerPairLaw (O.L.baseChange (resPt A ≫ Λ.σA))
      (Λ.L.baseChange (resPt A ≫ Λ.σA)) O.abqFibre (fun i => O.abqFibre_mul i)
    ∃ φ : pullback (KL.schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) ≅ pullback ψ ψ,
      φ.hom ≫ pullback.snd ψ ψ = pullback.snd _ _ := by sorry
