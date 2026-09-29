-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_ptsSp_symm_fibreMap_abqFibre_comp_eq_of_degeneracyHom_heckeGen_self
-- name    : ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_fibreMap_abqFibre_comp_eq_of_degeneracyHom_heckeGen_self
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/eb8d469b-49a1-5ded-8be1-30eb2d76dbd4
-- title:
--   Uₚ on the two special-fibre coordinates at p
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$, $p$ prime and $p \nmid N_0$, a valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$ and with residue field $\kappa =$ `ResidueField A` of characteristic $p$, a level datum $\Lambda$ of type `LevelData N₀ p A` (a structure morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` compatible with the generic point, a scheme $\mathcal A$ with morphism $\Lambda.f$ to `base p`, a relative group law $\Lambda.L$ on it, and bijections $\Lambda.\mathrm{pts}$ from $JZero\,N_0 = \operatorname{Pic}^0$ of the level-$N_0$ modular function field over $\overline{\mathbb Q}$ onto the sections of $\Lambda.f$ over the generic point and $\Lambda.\mathrm{ptsSp}$ from $JZeroC\,\kappa\,N_0$ onto the sections over `resPt A ≫ Λ.σA`) satisfying $\Lambda.\mathrm{IsJacobian}$ (abelian-scheme properties, commutativity of $\Lambda.L$, additivity and Galois equivariance of $\Lambda.\mathrm{pts}$, additivity of $\Lambda.\mathrm{ptsSp}$, agreement of reduction mod $\ell$ with $\Lambda.\mathrm{ptsSp}$, and realisability of every Hecke element by an endomorphism), and a Néron object $O$ of type `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with $G \to$ `base p` its underlying group scheme. Let $\varphi$ be an endomorphism of $G$ over `base p` which is a homomorphism for $O.L$ (composition with $\varphi$ commutes with $O.L.\mathrm{mul}$ on sections over any base), and let $\varphi'$ be an endomorphism of $\mathcal A$ over `base p` which realises the Hecke generator at $p$ on points, i.e. $(\Lambda.\mathrm{pts}(X_p \cdot x)).1 = (\Lambda.\mathrm{pts}\,x).1$ followed by $\varphi'$ for all $x \in JZero\,N_0$, for the module structure `heckeModuleBar N₀`. Assume, as identities of morphisms $G \to \mathcal A$ computed in $\Lambda.L$, that $\varphi$ followed by $O.\mathrm{degeneracyHom}\,0$ equals the $\Lambda.L$-product of ($O.\mathrm{degeneracyHom}\,0$ followed by $\varphi'$) with the $\Lambda.L$-inverse of $O.\mathrm{degeneracyHom}\,1$, and that $\varphi$ followed by $O.\mathrm{degeneracyHom}\,1$ equals the $p$-fold $\Lambda.L$-multiple of $O.\mathrm{degeneracyHom}\,0$. Then for every section $z$ of $O.g$ over `resPt A ≫ Λ.σA`, writing $\nu_i(z) = \Lambda.\mathrm{ptsSp}^{-1}(\mathrm{fibreMap}\,(O.\mathrm{abqFibre}\,i)\,z) \in JZeroC\,\kappa\,N_0$ for $i = 0, 1$, one has $\nu_0(z \text{ followed by } \varphi) = \mathrm{frobeniusPullbackModL}\,\kappa\,N_0\,p\,(\nu_0(z)) + (p-1)\,\nu_1(z)$ and $\nu_1(z \text{ followed by } \varphi) = O.\mathrm{frobSp}(\nu_1(z))$.
--
--   This is the formal counterpart of the description, going back to Deligne–Rapoport and used by Ribet, of the action of $U_p$ on the special fibre at $p$ of the Jacobian at level $N_0 p$: in the two coordinates coming from the degeneracy maps to level $N_0$, $U_p$ acts through the matrix with rows $(V, p-1)$ and $(0, F)$, $V$ being Frobenius pull-back and $F$ the Frobenius of the Néron object. It is used in [`ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero`](thm.html#ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero) to produce nontrivial Hecke torsion from a point with nonzero coordinates.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_ptsSp_symm_fibreMap_abqFibre_comp_eq_of_degeneracyHom_heckeGen_self.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JZeroNeronAtPData
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_ModularCurve_HeckeOperatorModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

open CategoryTheory CategoryTheory.Limits NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve ModularCurve.JZeroNeronObjectAtP
open AlgebraicGeometry
open ModularCurve

theorem ModularCurve.JZeroNeronObjectAtP.ptsSp_symm_fibreMap_abqFibre_comp_eq_of_degeneracyHom_heckeGen_self
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p) [CharP (ResidueField ↥A) p]
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (heckeGen ⟨p, Fact.out⟩ • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (hU0 : NeronModelInfra.schemeHomOverComp φ (O.degeneracyHom 0) =
      Λ.L.mul O.g (NeronModelInfra.schemeHomOverComp (O.degeneracyHom 0) φ') (Λ.L.inv O.g (O.degeneracyHom 1)))
    (hU1 : NeronModelInfra.schemeHomOverComp φ (O.degeneracyHom 1) = Λ.L.nsmul O.g p (O.degeneracyHom 0))
    (z : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    Λ.ptsSp.symm (fibreMap (O.abqFibre 0) (NeronModelInfra.schemeHomOverComp z φ)) =
        frobeniusPullbackModL (ResidueField ↥A) N₀ p (Λ.ptsSp.symm (fibreMap (O.abqFibre 0) z)) +
          (p - 1) • Λ.ptsSp.symm (fibreMap (O.abqFibre 1) z) ∧
      Λ.ptsSp.symm (fibreMap (O.abqFibre 1) (NeronModelInfra.schemeHomOverComp z φ)) =
        O.frobSp (Λ.ptsSp.symm (fibreMap (O.abqFibre 1) z)) := by sorry
