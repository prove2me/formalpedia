-- Prove2me | Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_muPt_comp_toricLift_eq_comp_fibreRestrictAlong
-- name    : ModularCurve.JZeroNeronObjectAtP.exists_muPt_comp_toricLift_eq_comp_fibreRestrictAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/c9e1f6a9-90e6-570e-a797-e18aea99bb62
-- title:
--   Base-changed endomorphisms preserve the toric lift on ℚ̄-points
-- statement:
--   Fix natural numbers $N_0$ and $p$ with $N_0 \neq 0$ and $p$ prime, and assume $p \nmid N_0$. Let $A$ be a valuation subring of an algebraic closure of $\mathbb Q$ with `A.LiesOverPrime p`, that is, $p$ lies in the non-units of $A$; let $\Lambda$ be a level datum for $(N_0,p,A)$ (in particular supplying a structure morphism $\sigma_A \colon \operatorname{Spec} A \to$ `base p` $= \operatorname{Spec}$ of the base ring at $p$) satisfying `Λ.IsJacobian`, and let $O$ be a Néron object `JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ`, with structure morphism $g \colon G \to$ `base p`, relative group law $L$, toric rank $t =$ `O.toricRank` and toric lifts `O.toricLift`. Let $\varphi$ be a morphism $G \to G$ over `base p` which is multiplicative for $L$, in the sense that for every scheme $T$ with a morphism $s \colon T \to$ `base p` and all $T$-points $x,y$ of $g$ one has $L_s(x,y)$ followed by $\varphi$ equal to $L_s(x \circ \varphi, y \circ \varphi)$. Let $m > 0$ and let $\chi$ be an $A$-algebra homomorphism from `muCoord ↥A t m` $= A[(\mathbb Z/m)^t]$ (the group algebra whose spectrum is $\mu_m^t$ over $A$) to the algebraic closure of $\mathbb Q$, giving via `muPt` a $\bar{\mathbb Q}$-point of $\mu_m^t$ over $A$. The assertion is that there exists another such $A$-algebra homomorphism $\chi'$ for which `muPt A t m χ'` followed by `O.toricLift m hm` equals `muPt A t m χ` followed by `O.toricLift m hm` followed by `fibreRestrictAlong Λ.σA O.g O.g φ`, the endomorphism of the pullback $G \times_{\mathrm{base}~p} \operatorname{Spec} A$ induced by $\varphi$; that is, the image under the base-changed $\varphi$ of the toric lift of $\chi$ is again the toric lift of a $\bar{\mathbb Q}$-point of $\mu_m^t$.
--
--   This is the geometric core of the statement that the subgroup of toric points of the Néron object is stable under the Hecke action: an $L$-multiplicative endomorphism of $G$, base changed to the valuation ring $A$, maps toric lifts of $m$-torsion characters to toric lifts. It is used by [`ModularCurve.JZeroNeronObjectAtP.smul_mem_toricPts`](thm.html#ModularCurve.JZeroNeronObjectAtP.smul_mem_toricPts), and is proved from the description of the action of $\varphi$ on the special-fibre torus by an integral character matrix together with a rigidity statement identifying two such lifts.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZeroNeronObjectAtP_exists_muPt_comp_toricLift_eq_comp_fibreRestrictAlong.lean

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra NeronSpecialFibreInfra GoodReductionJacobian
  ModularCurve IsLocalRing ModularCurve.JZeroNeronObjectAtP

theorem ModularCurve.JZeroNeronObjectAtP.exists_muPt_comp_toricLift_eq_comp_fibreRestrictAlong
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (Λ : JZeroNeronObjectAtP.LevelData N₀ p A) (hΛ : Λ.IsJacobian)
    (O : JZeroNeronObjectAtP N₀ p hpN₀ A hA Λ)
    (φ : SchemeHomOver O.g O.g)
    (hφ : ∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s O.g),
      NeronModelInfra.schemeHomOverComp (O.L.mul s x y) φ =
        O.L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ))
    (m : ℕ) (hm : 0 < m) (χ : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ) :
    ∃ χ' : muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ,
      NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ') (O.toricLift m hm) =
        NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp (muPt A O.toricRank m χ) (O.toricLift m hm))
          (fibreRestrictAlong Λ.σA O.g O.g φ) := by sorry
