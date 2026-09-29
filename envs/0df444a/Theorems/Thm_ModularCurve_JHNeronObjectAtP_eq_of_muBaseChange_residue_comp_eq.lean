-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
-- name    : ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/5822b556-6d43-57b7-bb55-c9ab8fd4f435
-- title:
--   Rigidity of A-morphisms μ_m^t → G_A on the special fibre
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$, let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$, whose residue field is algebraically closed of characteristic $p$. Let $\Lambda$ be level data for the $\Gamma_H(M)$-Néron object at $p$ — in particular a morphism $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb{Z}_{(p)}$ lifting the generic point — and let $O$ be a $\Gamma_H(M)$-Néron object at $p$ over $\Lambda$, with structure morphism $g \colon G \to \operatorname{Spec} \mathbb{Z}_{(p)}$, relative group law $L$, and toric rank $t = O.\mathrm{toricRank}$. Let $m > 0$, write $\mu = \operatorname{Spec} A[(\mathbb{Z}/m)^{t}]$ for the diagonalisable $A$-group scheme of type $(\mathbb{Z}/m)^{t}$, and write $G_A = G \times_{\operatorname{Spec} \mathbb{Z}_{(p)}} \operatorname{Spec} A$ with its base-changed group law $L_A$. Let $u, v \colon \mu \to G_A$ be morphisms of $A$-schemes (each given together with the identity that composing with the structure morphism of $G_A$ returns that of $\mu$) such that each is multiplicative on $\overline{\mathbb{Q}}$-points: for all $\chi, \chi'$ in the convolution monoid of $A$-algebra maps $A[(\mathbb{Z}/m)^{t}] \to \overline{\mathbb{Q}}$, the point of $G_A$ obtained by composing the point attached to $\chi \ast \chi'$ with $u$ (respectively $v$) equals the $L_A$-product of the points obtained from $\chi$ and from $\chi'$. Assume finally that $u$ and $v$ agree after pullback along the base change $\operatorname{Spec} k[(\mathbb{Z}/m)^{t}] \to \operatorname{Spec} A[(\mathbb{Z}/m)^{t}]$ induced by the residue map of $A$, i.e. on the special fibre. Then $u = v$.
--
--   This is the rigidity statement for homomorphisms from a group of multiplicative type over a henselian local base, in the form needed for the Néron model of $J_H(M)$ at $p$: a morphism from $\mu_m^t$ to the base-changed Néron object is determined by its restriction to the special fibre. It is used in the construction and comparison of toric lifts, and hence in the description of the toric part of the reduction, in the level-lowering argument at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

theorem ModularCurve.JHNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) (hm : 0 < m)
    (u v : SchemeHomOver (muStr ↥A O.toricRank m) (RelativeGroupLaw.baseChangeStr Λ.σA O.g))
    (hu : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) u =
        (O.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) u)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) u))
    (hv : ∀ χ χ' : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ),
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m (χ * χ').ofConv) v =
        (O.L.baseChange Λ.σA).mul _ (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ.ofConv) v)
          (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ'.ofConv) v))
    (huv : muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ u.1 =
      muBaseChange (IsLocalRing.residue ↥A) O.toricRank m ≫ v.1) :
    u = v := by sorry
