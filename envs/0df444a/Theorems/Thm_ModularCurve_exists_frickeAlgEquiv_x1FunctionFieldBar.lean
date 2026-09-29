-- Prove2me | Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar
-- name    : ModularCurve.exists_frickeAlgEquiv_x1FunctionFieldBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/d7ceb7a5-629e-534d-a808-f970a115a04a
-- title:
--   Fricke involution package for J₁(M) over ℚ̄
-- statement:
--   Let $M \ge 1$. Write $F =$ `x1FunctionFieldBar M` for the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise images of the $q$-expansion function field of $X_1(M)$ over $\mathbb Q$, and `JOne M` $= \mathrm{Pic}^0_{\overline{\mathbb Q}}(F)$, the group of degree-zero divisors on the places of $F$ over $\overline{\mathbb Q}$ modulo those recording the orders of nonzero elements. The assertion is that there exists a $\overline{\mathbb Q}$-algebra automorphism $w$ of $F$ such that, with $w$ acting on `JOne M` through the semilinear automorphism $(w,\mathrm{id})$, the following four statements hold. First, for every prime $\ell$ and every choice of auxiliary data — integrality of the two $\overline{\mathbb Q}$-algebra maps $\alpha =$ `heckeAlphaOneBar` (the inclusion into the base-changed field of $\Gamma_1(M) \cap \Gamma_0(M\ell)$) and $\beta =$ `heckeBetaOneBar` (the map induced by $q \mapsto q^{\ell}$ if that lands in the larger field, and $\alpha$ otherwise), existence of principal divisors of degree zero on that larger field, the fundamental identity along $\beta$ and along $\alpha$, finiteness along $\alpha$ and along $\beta$ with the pushforward norm formula in each case — one has $(\beta_* \circ \alpha^*)(w \cdot x) = w \cdot (\alpha_* \circ \beta^*)(x)$ for all $x$ in `JOne M`. Second, $\langle d\rangle_*(w \cdot \langle d\rangle_* x) = w \cdot x$ for every $d \in \mathbb N$ and every $x$, where $\langle d\rangle_*$ is `diamondOneBar M d`. Third, $w \cdot (w \cdot x) = x$. Fourth, for every prime $p \nmid M$, every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a nonunit of $A$, and every $\tau$ in the image in $\overline{\mathbb Q} \simeq_{\mathbb Q} \overline{\mathbb Q}$ of the inertia subgroup of $A$ over $\mathbb Q$, the actions of $w$ and of $\tau$ on `JOne M` commute.
--
--   This is the Fricke involution $w_M$ of $X_1(M)$, packaged as the list of properties of its induced action on $J_1(M)(\overline{\mathbb Q})$ that the later argument uses: it transposes every Hecke correspondence, inverts the diamond operators in the stated conjugated form, is an involution, and commutes with inertia at primes of good reduction. It is obtained from the corresponding statement for the curves $X_H(M)$ and feeds the construction of the self-adjointness pairing on the Tate module of $J_1(M)$ in [`ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le`](thm.html#ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_reductionKernelSpan_orthogonal_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_x1FunctionFieldBar (M : ℕ) [NeZero M] :
    ∃ w : x1FunctionFieldBar M ≃ₐ[AlgebraicClosure ℚ] x1FunctionFieldBar M,
      (∀ (ℓ : ℕ) [Fact ℓ.Prime]
          (hα : HeckeAlphaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          (hβ : HeckeBetaOneBarIntegral (AlgebraicClosure ℚ) M ℓ)
          [HasPrincipalDivisors (AlgebraicClosure ℚ)
            (laurentBaseChange (AlgebraicClosure ℚ) (x1x0FunctionFieldC ℚ M (M * ℓ)))]
          (hFIβ : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hβ)
          (hfinα : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNα : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hfinα)
          (hFIα : FundamentalIdentityAlong (AlgebraicClosure ℚ)
            (heckeAlphaOneBar (AlgebraicClosure ℚ) M ℓ) hα)
          (hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ))
          (hNβ : NormFormulaAlong (AlgebraicClosure ℚ)
            (heckeBetaOneBar (AlgebraicClosure ℚ) M ℓ) hfinβ)
          (x : JOne M),
        heckePic0OneBarTranspose hα hβ hFIα hfinβ hNβ (SemilinearAut.ofAlgAut w • x)
          = SemilinearAut.ofAlgAut w • heckePic0OneBar hα hβ hFIβ hfinα hNα x) ∧
      (∀ (d : ℕ) (x : JOne M),
        diamondOneBar M d (SemilinearAut.ofAlgAut w • diamondOneBar M d x)
          = SemilinearAut.ofAlgAut w • x) ∧
      (∀ x : JOne M, SemilinearAut.ofAlgAut w • (SemilinearAut.ofAlgAut w • x) = x) ∧
      (∀ (p : ℕ), p.Prime → ¬ p ∣ M → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
        A.LiesOverPrime p → ∀ τ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JOne M,
          SemilinearAut.ofAlgAut w • (τ • x) = τ • (SemilinearAut.ofAlgAut w • x)) := by sorry
