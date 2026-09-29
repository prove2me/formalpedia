-- Prove2me | Theorems.Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
-- name    : ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/519d1fcd-de43-5d28-8aaa-d09e277bafcf
-- title:
--   Diamond tokens are multiplicative and trivial on H'
-- statement:
--   Fix a field $K$, a positive integer $N$ and a subgroup $H' \le (\mathbb{Z}/N)^{\times}$. Write $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H')`](def/ModularCurve_X1.html#L101) for the subfield of $K((q))$ generated over $K$ by the quotients $\mathrm{intSeriesC}_K(p_f)/\mathrm{intSeriesC}_K(p_g)$ of integral $q$-expansions of modular forms of equal weight for $\Gamma_{H'}(N)$ (the image in $\mathrm{SL}_2(\mathbb{Z})$ of the preimage of $H'$ under [`CohCarrier.gamma0Units`](def/CohCarrier_Level.html#L121)), and let $\rho =$ [`ModularCurve.diamondActionModL K N H'`](def/ModularCurve_XHDifferentialsModL.html#L203) $\colon \Gamma_0(N) \to (F \simeq_{\mathrm{alg}[K]} F)$ be the homomorphism chosen to satisfy the pull-back property `IsDiamondPullbackModL` when such a homomorphism exists and equal to the trivial homomorphism otherwise; for $d \in (\mathbb{Z}/N)^{\times}$ let $\sigma_d =$ [`CuspForm.gammaLift N d`](def/CuspForm_HeckeOperatorFormsGammaH.html#L36) be the chosen element of $\Gamma_0(N)$ with `gamma0Units` value $d$. The theorem asserts, unconditionally, the conjunction of seven statements: $\rho(\sigma_{dd'}) = \rho(\sigma_d)\rho(\sigma_{d'})$ for all $d, d'$; $\rho(\sigma_d) = 1$ for $d \in H'$; $\rho(\sigma_d) = \rho(\sigma_{d'})$ whenever $d d'^{-1} \in H' \sqcup \langle -1 \rangle$; $\rho(\sigma_d)\rho(\sigma_{d^{-1}}) = 1$; and the corresponding three statements transported through the monoid homomorphism [`AlgebraicCurve.SemilinearAut.ofAlgAut`](def/AlgebraicCurve_BaseChangeGalois.html#L76), which sends a $K$-automorphism $\tau$ of $F$ to the pair $(\tau, 1)$ in the group of ring automorphisms of $F$ compatible over $K$ with a ring automorphism of $K$: for every type $X$ (in a fixed universe) carrying an action of [`AlgebraicCurve.SemilinearAut K F`](def/AlgebraicCurve_BaseChangeGalois.html#L15), every $x \in X$ and all $d, d'$, one has $\langle dd'\rangle \cdot x = \langle d \rangle \cdot (\langle d' \rangle \cdot x)$, $\langle d \rangle \cdot x = x$ when $d \in H'$, and $\langle d \rangle \cdot (\langle d^{-1}\rangle \cdot x) = x = \langle d^{-1}\rangle \cdot (\langle d \rangle \cdot x)$, where $\langle d \rangle$ denotes `ofAlgAut`$(\rho(\sigma_d))$.
--
--   This packages the standard fact that the diamond operators $\langle d \rangle$ on the modular curve $X_{H'}(N)$ form an action of $(\mathbb{Z}/N)^{\times}$ that factors through $(\mathbb{Z}/N)^{\times}/\langle H', -1\rangle$, in the form needed for the chosen reduced diamond action on the $q$-expansion function field and for its semilinear incarnation on auxiliary carriers such as places, divisors and degree-zero divisor classes. It is used by the statements about fixed places, differentials and Néron objects at $p$ that invoke the diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open scoped MatrixGroups

theorem ModularCurve.diamondActionModL_gammaLift_mul_and_eq_one_of_mem_and_ofAlgAut_smul
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (H' : Subgroup (ZMod N)ˣ) :
    (∀ d d' : (ZMod N)ˣ,
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N (d * d')) =
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) *
            ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) ∧
    (∀ d : (ZMod N)ˣ, d ∈ H' → ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) = 1) ∧
    (∀ d d' : (ZMod N)ˣ, d * d'⁻¹ ∈ H' ⊔ Subgroup.zpowers (-1 : (ZMod N)ˣ) →
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) =
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) ∧
    (∀ d : (ZMod N)ˣ,
        ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d) *
          ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹) = 1) ∧

    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d d' : (ZMod N)ˣ),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N (d * d'))) • x =
          AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d')) • x) ∧
    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d : (ZMod N)ˣ), d ∈ H' →
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) • x = x) ∧
    (∀ (X : Type u) [MulAction (AlgebraicCurve.SemilinearAut K ↥(ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH N H'))) X]
        (x : X) (d : (ZMod N)ˣ),
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)) • x = x ∧
        AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d⁻¹)) •
            AlgebraicCurve.SemilinearAut.ofAlgAut (ModularCurve.diamondActionModL K N H' (CuspForm.gammaLift N d)) • x = x) := by sorry
