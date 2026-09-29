-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
-- name    : ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/2b8c844b-d1f0-511a-bcee-5c28d2d00ede
-- title:
--   Endomorphisms act on the special-fibre torus through a lattice map
-- statement:
--   Fix natural numbers $p$ and $M$ with $p$ prime and $M \neq 0$, a subgroup $H \le (\mathbb{Z}/M)^{\times}$, and a divisibility $p \mid M$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a nonunit of $A$ (the predicate `LiesOverPrime`), whose residue field $\kappa =$ `ResidueField ↥A` is of characteristic $p$ and algebraically closed. Let $\Lambda$ be a level datum at $p$ for level $\Gamma_H(M)$: a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ lifting the generic point, a scheme $X$ with structure morphism $f$ to $\operatorname{Spec} \mathbb{Z}_{(p)}$ carrying a relative group law, and bijections identifying the points of $J_H(M/p)$ at the generic point and $\operatorname{Pic}^0$ of the residue-field curve at $\operatorname{resPt} A \mathbin{\scriptstyle\circ} \sigma_A$ with the corresponding sections of $f$; assume $\Lambda.f$ satisfies `AbelianSchemePropertyBundle`, i.e. it is smooth and proper with connected fibres and admits a relative group law. Let $O$ be a Néron object at $p$ for $\Lambda$, with structure morphism $g \colon G \to \operatorname{Spec} \mathbb{Z}_{(p)}$, toric rank $t = O.\mathrm{toricRank}$ and special-fibre torus morphism $O.\mathrm{torusFibre}$, whose underlying morphism goes from $\operatorname{Spec} \kappa[\mathbb{Z}^t]$ to the fibre product of $g$ with $\operatorname{resPt} A \mathbin{\scriptstyle\circ} \sigma_A$. Let $\varphi$ be a morphism $G \to G$ over $\operatorname{Spec} \mathbb{Z}_{(p)}$ which is additive for the group law, in the sense that for every scheme $T$ with a morphism $s \colon T \to \operatorname{Spec} \mathbb{Z}_{(p)}$ and all sections $x, y$ of $g$ over $s$, post-composing the sum $O.L.\mathrm{mul}\,s\,x\,y$ with $\varphi$ gives the sum of the post-compositions. The conclusion asserts the existence of an additive monoid endomorphism $M_0$ of $\mathbb{Z}^t = (\mathrm{Fin}\,t \to \mathbb{Z})$ such that the torus endomorphism $\operatorname{Spec}$ of the induced ring endomorphism $\kappa[\mathbb{Z}^t] \to \kappa[\mathbb{Z}^t]$ (`AddMonoidAlgebra.mapDomainRingHom` applied to $M_0$), followed by $O.\mathrm{torusFibre}$, equals $O.\mathrm{torusFibre}$ followed by the morphism induced by $\varphi$ on the fibre over $\operatorname{resPt} A \mathbin{\scriptstyle\circ} \sigma_A$ via `fibreRestrictAlong` (the lift of $\mathrm{pr}_1$ followed by $\varphi$ together with $\mathrm{pr}_2$).
--
--   This expresses that an endomorphism of the Néron model which respects the group law preserves the split torus inside the special fibre at $p$, acting on it through an endomorphism of its character lattice $\mathbb{Z}^t$; it is the level-$\Gamma_H(M)$ counterpart of the corresponding statement for level $\Gamma_0$. It is used to compute the action of the Hecke operator $U_p$ and of the Galois action on toric points and on the toric lattice, in the analysis of the character group of the torus in Ribet's level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.exists_mapDomain_comp_torusFibre_eq_torusFibre_comp_fibreRestrictAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφmul : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) :
    ∃ M₀ : (Fin O.toricRank → ℤ) →+ (Fin O.toricRank → ℤ),
      Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom (ResidueField ↥A) M₀)) ≫ O.torusFibre.1 =
        O.torusFibre.1 ≫ (fibreRestrictAlong (resPt A ≫ Λ.σA) O.g O.g φ).1 := by sorry
