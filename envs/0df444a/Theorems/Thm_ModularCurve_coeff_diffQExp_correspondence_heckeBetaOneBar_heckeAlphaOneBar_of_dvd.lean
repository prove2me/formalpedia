-- Prove2me | Theorems.Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
-- name    : ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/fc947c20-3ac2-5e1a-8b0f-02cbccb622e6
-- title:
--   U_ℓ on q-expansions of differentials of X₁(M)
-- statement:
--   Fix a nonzero natural number $M$, a prime $\ell$ with $\ell \mid M$, and assume [`ModularCurve.HeckeBetaOneDefined M ℓ`](def/ModularCurve_X1HeckeOperator.html#L84), i.e. that for every $y$ in `x1FunctionField M` the substitution `qExpand ℚ ℓ y` lies in `x1x0FunctionFieldC ℚ M (M * ℓ)`. Write $\bar{K} =$ `AlgebraicClosure ℚ` and let $F =$ `x1FunctionFieldBar M` be the base change to $\bar{K}$ of the $q$-expansion function field of $X_1(M)$, an intermediate field of $\bar{K}((q))$ over $\bar{K}$. Let $\omega \in \Omega[F⁄\bar{K}]$ be a Kähler differential and $n$ an integer. Consider the two $\bar{K}$-algebra maps from $F$ into the base change of `x1x0FunctionFieldC ℚ M (M * ℓ)`: `heckeAlphaOneBar`, the inclusion, and `heckeBetaOneBar`, which under the given hypothesis is the branch `heckeBetaOneBarOf` attached to the substitution `qExpand ℚ ℓ`. Then [`AlgebraicCurve.Differential.correspondence`](def/AlgebraicCurve_DifferentialPushPull.html#L69) applied to this pair, namely pull-back along `heckeAlphaOneBar` followed by the trace along `heckeBetaOneBar`, sends $\omega$ to a differential whose $q$-expansion under `diffQExp` (the lift of the derivation $q\,d/dq$, so that $\eta \mapsto f$ when $\eta = f\,dq/q$) has $n$-th Laurent coefficient equal to the $(n\ell)$-th coefficient of the $q$-expansion of $\omega$.
--
--   This is the computation that the Hecke correspondence at a prime $\ell$ dividing the level acts on $q$-expansions of differentials of $X_1(M)$ exactly as the operator $U_\ell \colon \sum a_n q^n \mapsto \sum a_{\ell n} q^n$, with no further term and no scaling factor; the degree of the relevant map is $\ell$ in this case, as recorded by [`ModularCurve.finrankAlong_heckeBetaOneBar`](thm.html#ModularCurve.finrankAlong_heckeBetaOneBar). It feeds the comparison of Hecke operators on the Jacobian with Hecke operators on weight-two cusp forms via $f \mapsto f(q)\,dq/q$, and is used in [`ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff`](thm.html#ModularCurve.exists_injective_ringHom_adjoin_heckeDiamondGenBar_cuspForm_qCoeff).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeOperator
import Definitions.Def_ModularCurve_HeckeDifferential

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem ModularCurve.coeff_diffQExp_correspondence_heckeBetaOneBar_heckeAlphaOneBar_of_dvd
    (M : ℕ) [NeZero M] (ℓ : ℕ) [Fact ℓ.Prime] (hℓM : ℓ ∣ M)
    (hβ : ModularCurve.HeckeBetaOneDefined M ℓ)
    (ω : Ω[↥(ModularCurve.x1FunctionFieldBar M)⁄AlgebraicClosure ℚ]) (n : ℤ) :
    (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M)
        (AlgebraicCurve.Differential.correspondence
          (ModularCurve.heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ)
          (ModularCurve.heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) ω)).coeff n =
      (ModularCurve.diffQExp (ModularCurve.x1FunctionFieldBar M) ω).coeff (n * ℓ) := by sorry
