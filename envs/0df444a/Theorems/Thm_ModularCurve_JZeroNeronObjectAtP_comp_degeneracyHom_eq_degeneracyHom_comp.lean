-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp
-- name    : ModularCurve.JZeroNeronObjectAtP.comp_degeneracyHom_eq_degeneracyHom_comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e384094a-3d49-59ae-952c-d1ff8b7284cd
-- title:
--   Degeneracy morphisms intertwine Hecke endomorphisms over the base
-- statement:
--   Fix natural numbers $N_0, p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure $\overline{\mathbb Q}$ of $\mathbb Q$ with $p$ a nonunit of $A$ (the predicate `LiesOverPrime`), let $\Lambda$ be a level datum of type `LevelData N₀ p A` — a scheme $\Lambda.X$ with a structure morphism $\Lambda.f$ to `base p`, a relative group law over `baseRing p`, a section $\sigma_A$ from $\operatorname{Spec} A$ compatible with the generic point, and bijections of $\mathrm{JZero}\,N_0 = \mathrm{Pic}^0$ of the level-$N_0$ modular function field over $\overline{\mathbb Q}$ with the sections of $\Lambda.f$ over the generic point, and of the corresponding residue-field $\mathrm{Pic}^0$ with the sections over the special point — satisfying $\Lambda.\mathrm{IsJacobian}$ (abelian scheme property bundle, commutativity, additivity and Galois equivariance of both point parametrisations, compatibility of reduction, and existence of Hecke endomorphisms). Let $O$ be an object of `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`: a smooth, separated, locally of finite type, quasi-compact and surjective $G \to$ `base p` with connected fibres, a commutative relative group law, a bijection $O.\mathrm{pts}$ from $\mathrm{JZero}(N_0 p)$ onto the sections of $O.g$ over the generic point which is additive, Galois-equivariant and Hecke-compatible, with flat surjective multiplication-by-$n$ maps and proper generic fibre, together with the degeneracy morphisms $O.\mathrm{degeneracyHom}\,i$ from $G$ to $\Lambda.X$ over `base p`, which satisfy $\Lambda.\mathrm{pts}(d_i x) = O.\mathrm{pts}(x)$ followed by $O.\mathrm{degeneracyHom}\,i$, where $d_i =$ `degeneracyPushforwardPair N₀ p i` is the additive map $\mathrm{JZero}(N_0p) \to \mathrm{JZero}\,N_0$ given by $\mathrm{Pic}^0$ push-forward along $\bar\alpha$ for $i=0$ and along $\bar\beta$ for $i=1$ (and zero if the relevant inputs fail). Fix $i \in \{0,1\}$ and $t, t'$ in the Hecke algebra $\mathbb Z[\,$primes$\,]$. Let $\varphi : G \to G$ over `base p` induce $t$ on points, i.e. $O.\mathrm{pts}(t \cdot x) = O.\mathrm{pts}(x)$ followed by $\varphi$ for all $x \in \mathrm{JZero}(N_0p)$, and let $\varphi' : \Lambda.X \to \Lambda.X$ over `base p` induce $t'$ on $\mathrm{JZero}\,N_0$ in the same sense, the module structures being `heckeModuleBar` at levels $N_0p$ and $N_0$. Assume $d_i(t \cdot x) = t' \cdot d_i(x)$ for all $x \in \mathrm{JZero}(N_0p)$. Then $\varphi$ followed by $O.\mathrm{degeneracyHom}\,i$ equals $O.\mathrm{degeneracyHom}\,i$ followed by $\varphi'$, as morphisms $G \to \Lambda.X$.
--
--   This is the scheme-theoretic upgrade, by density of the generic fibre, of an intertwining relation between Hecke correspondences and the degeneracy push-forwards: the relation, known on $\overline{\mathbb Q}$-points of the Jacobians, is transported to the integral models over the local base at $p$. It is used in the analysis of the Hecke action on the toric part of the special fibre, namely by [`ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_ptsSp_symm_fibreMap_abqFibre_ne_zero`](thm.html#ModularCurve.JZeroNeronObjectAtP.hasLowerLevelTorsion_of_ptsSp_symm_fibreMap_abqFibre_ne_zero) and [`ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero`](thm.html#ModularCurve.JZeroNeronObjectAtP.heckeTorsion_ne_bot_of_ptsSp_symm_fibreMap_abqFibre_ne_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_comp_degeneracyHom_eq_degeneracyHom_comp.lean

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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian ModularCurve IsLocalRing
  AlgebraicCurve ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.comp_degeneracyHom_eq_degeneracyHom_comp
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (i : Fin 2) (t t' : HeckeAlg)
    (φ : SchemeHomOver O.g O.g)
    (hφt : letI := heckeModuleBar (N₀ * p); ∀ x : JZero (N₀ * p), (O.pts (t • x)).1 = (O.pts x).1 ≫ φ.1)
    (φ' : SchemeHomOver Λ.f Λ.f)
    (hφ't : letI := heckeModuleBar N₀; ∀ x : JZero N₀, (Λ.pts (t' • x)).1 = (Λ.pts x).1 ≫ φ'.1)
    (hdeg : ∀ x : JZero (N₀ * p),
      degeneracyPushforwardPair N₀ p i (letI := heckeModuleBar (N₀ * p); t • x) =
        (letI := heckeModuleBar N₀; t' • degeneracyPushforwardPair N₀ p i x)) :
    φ.1 ≫ (O.degeneracyHom i).1 = (O.degeneracyHom i).1 ≫ φ'.1 := by sorry
