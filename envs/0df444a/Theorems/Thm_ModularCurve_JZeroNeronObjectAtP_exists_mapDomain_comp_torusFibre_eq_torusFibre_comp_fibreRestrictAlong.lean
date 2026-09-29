-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/268d41c6-3a83-5049-b24e-0b641558c7c1
-- title:
--   Endomorphisms act on the special-fibre torus by a character matrix
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0$ and $p$ nonzero, $p$ prime and $p \nmid N_0$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $A$. Let $\Lambda$ be a `LevelData N₀ p A`, consisting of a structure morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` compatible with the generic point, a scheme $X$ over `base p` with a relative group law and prescribed parametrisations of its generic and residual points, and assume $\Lambda$ satisfies `IsJacobian` (abelian-scheme property bundle, commutativity of the group law, additivity and Galois equivariance of the point parametrisations, compatibility of reduction, and existence of Hecke endomorphisms). Let $O$ be a `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with structure morphism $g \colon G \to$ `base p` and relative group law $O.L$. Let $\varphi$ be a morphism $G \to G$ over $g$ which is additive for $O.L$: for every scheme $T$ with a morphism $s$ to `base p` and all $T$-points $x, y$ of $G$ over $s$, composing $O.L.\mathrm{mul}\,s\,x\,y$ with $\varphi$ equals $O.L.\mathrm{mul}\,s$ applied to $x$ followed by $\varphi$ and $y$ followed by $\varphi$. Then there exists an additive endomorphism $M_0$ of $\mathbb Z^{O.\mathrm{toricRank}}$ such that the endomorphism of $\operatorname{Spec}$ of the group algebra $\kappa(A)[\mathbb Z^{O.\mathrm{toricRank}}]$ induced by $M_0$ through `AddMonoidAlgebra.mapDomainRingHom`, followed by the underlying morphism of $O.\mathrm{torusFibre}$, agrees with $O.\mathrm{torusFibre}$ followed by the restriction of $\varphi$ to the fibre over the residue point $\operatorname{Spec}\kappa(A) \to \operatorname{Spec} A \to$ `base p` given by `fibreRestrictAlong`.
--
--   This is the rigidity statement that an additive endomorphism of the Néron object $G$ attached to $J_0(N_0p)$ acts on the split torus sitting inside the special fibre at $p$ through a matrix of characters, i.e. through an additive endomorphism of the character lattice $\mathbb Z^{\mathrm{toricRank}}$; it rests on the absence of non-constant morphisms from a split torus to an abelian variety over the algebraically closed residue field. It is used to produce the lattice-level action of Hecke operators on the toric points of the special fibre, and thence in the analysis of the Galois representation at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
        O.torusFibre.1 ≫ (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ).1 := by sorry
