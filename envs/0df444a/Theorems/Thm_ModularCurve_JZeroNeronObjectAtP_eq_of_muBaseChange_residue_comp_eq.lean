-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq
-- name    : ModularCurve.JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e6998921-6079-55c1-ad5c-751e390a6afd
-- title:
--   Rigidity of μ_m^t-homomorphisms over a henselian valuation base
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A \subseteq \overline{\mathbb Q}$ be a valuation subring lying over $p$, in the sense that $p$ is a non-unit of $A$, let $\Lambda$ be a `LevelData` for $(N_0,p,A)$ satisfying `IsJacobian`, and let $O$ be a `JZeroNeronObjectAtP` for these data, with structure morphism $g \colon G \to \operatorname{Spec} \mathbb Z_{(p)}$, relative group law $O.L$ and toric rank $t = O.\mathrm{toricRank}$. Let $m > 0$. Write $\mu = \operatorname{Spec} A[(\mathbb Z/m)^t]$, the spectrum of the group algebra `AddMonoidAlgebra A (Fin t → ZMod m)`, viewed over $\operatorname{Spec} A$, and let $G_A$ be the pullback of $g$ along $\sigma_A \colon \operatorname{Spec} A \to \operatorname{Spec} \mathbb Z_{(p)}$, with its base-changed group law. Let $u$ and $v$ be two morphisms $\mu \to G_A$ over $\operatorname{Spec} A$. Assume that each of $u$ and $v$ is multiplicative on $\overline{\mathbb Q}$-points: for all $\chi, \chi'$ in the convolution monoid `WithConv` of $A$-algebra homomorphisms $A[(\mathbb Z/m)^t] \to \overline{\mathbb Q}$, composing the point $\operatorname{Spec}(\chi\chi')$ of $\mu$ with $u$ (respectively $v$) gives the product, under the base-changed law, of the composites of $\operatorname{Spec}(\chi)$ and $\operatorname{Spec}(\chi')$ with $u$ (respectively $v$). Assume finally that $u$ and $v$ have the same restriction to the special fibre, i.e. their composites with the morphism $\operatorname{Spec} \kappa[(\mathbb Z/m)^t] \to \mu$ induced by the residue map $A \to \kappa$ agree. Then $u = v$.
--
--   This is the rigidity statement for homomorphisms from a group of multiplicative type over a henselian local base: a homomorphism into the Néron model is determined by its special fibre. It is used in the construction and comparison of toric lifts of points of $\mu_m^t$ into the Néron object at $p$, supplying the uniqueness half of those existence results.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_eq_of_muBaseChange_residue_comp_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.eq_of_muBaseChange_residue_comp_eq
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ) (m : ℕ) (hm : 0 < m)
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
