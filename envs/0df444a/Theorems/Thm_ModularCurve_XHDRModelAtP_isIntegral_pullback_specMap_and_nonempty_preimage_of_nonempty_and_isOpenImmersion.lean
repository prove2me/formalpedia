-- Prove2me | Theorems.Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
-- name    : ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.08657+00:00
-- url     : https://prove2.me/theorems/1b705c2f-f5c8-50a8-a183-89ad29f90f64
-- title:
--   Integrality of mathfrak X_{P_ℓ} and density of its geometric generic fibre
-- statement:
--   Fix a prime $p$, an integer $M \neq 0$ with $p \mid M$, a subgroup $H \le (\mathbb Z/M)^\times$, and a valuation subring $P_\ell$ of $\overline{\mathbb Q}$ satisfying `Pl.LiesOverPrime p`, i.e. the image of $p$ in $\overline{\mathbb Q}$ is a non-unit of $P_\ell$. Assume the Laurent series `jqModC ℚ` lies in the intermediate field `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the relevant $q$-expansion ratios for the full modular group, and let $\mathfrak X$ be a term of the structure [`ModularCurve.XHDRModelAtP p M H hpM hj`](def/ModularCurve_XHDRModelAtP.html#L81): a package consisting of the two-chart integral model `X p (ΓM M H) hj` over `Spec (R p)` together with properness, flatness, integrality, local finite presentation and normality hypotheses for its structure morphism `toBase p (ΓM M H) hj`, properness and smoothness of relative dimension $1$ at the auxiliary level `ΓN p M H hpM`, a curve model `𝔛.Meta` over $\overline{\mathbb Q}$ with function field `xHFunctionFieldBar M H`, an isomorphism `𝔛.eeta` from `𝔛.Meta.C` onto the base change of the model along `R p → AlgebraicClosure ℚ` compatible with the structure morphisms, Galois equivariance of the induced bijection between $\overline{\mathbb Q}$-points and places, and conditions pinning down the $q$-expansions on the finite chart. Let $\rho \colon R_p \to P_\ell$ be a ring homomorphism whose composite with the inclusion $P_\ell \hookrightarrow \overline{\mathbb Q}$ is the structure map of `R p`, and let $g_A$ be a morphism from `𝔛.Meta.C` to the fibre product of `toBase p (ΓM M H) hj` and `Spec.map ρ` whose first projection agrees with that of `𝔛.eeta` and whose second projection is `𝔛.Meta.toBase` followed by `Spec.map` of the inclusion $P_\ell \hookrightarrow \overline{\mathbb Q}$. Then the fibre product $\mathfrak X_{P_\ell}$ is an integral scheme; for every open subscheme $W$ of $\mathfrak X_{P_\ell}$ that is non-empty, the preimage $g_A^{-1}(W)$ is non-empty; and $g_A$ is an open immersion.
--
--   This is the base change to the valuation ring of a place above $p$ of the Deligne–Rapoport style integral model of $X_H(M)$, together with the identification of its geometric generic fibre as a dense open subscheme. It is the geometric input for the subsequent computations on the model over $P_\ell$, in particular for the divisor- and order-of-vanishing statements used in the analysis of Néron objects attached to $J_H$ at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRModelAtP_isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve
  ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

set_option maxHeartbeats 800000 in
open Classical in
open ModularCurve in

theorem ModularCurve.XHDRModelAtP.isIntegral_pullback_specMap_and_nonempty_preimage_of_nonempty_and_isOpenImmersion

    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : p ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (gA : 𝔛.Meta.C ⟶ (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))))
    (hgA₁ : gA ≫ pullback.fst _ _ = 𝔛.eeta ≫ pullback.fst _ _)
    (hgA₂ : gA ≫ pullback.snd _ _ = 𝔛.Meta.toBase ≫ barPt Pl) :
    IsIntegral (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ∧
    (∀ W : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).Opens,
        Nonempty (Scheme.Opens.toScheme W) → Nonempty (Scheme.Opens.toScheme (gA ⁻¹ᵁ W))) ∧
    IsOpenImmersion gA := by sorry
