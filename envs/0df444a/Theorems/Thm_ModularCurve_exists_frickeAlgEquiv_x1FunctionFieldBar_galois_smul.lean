-- Prove2me | Theorems.Thm_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
-- name    : ModularCurve.exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/7ade4197-1d06-5fc5-9721-5a09d7c5b556
-- title:
--   Fricke involution package for J₁(M) over ℚ̄
-- statement:
--   Let $M\ge 1$ be a natural number. Write $F=$ `x1FunctionFieldBar M` for the subfield of $\overline{\mathbb{Q}}((q))$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the rational $q$-expansion function field of $X_1(M)$, and $J_1(M)=$ `JOne M` for $\mathrm{Pic}^0$ of $F$ over $\overline{\mathbb{Q}}$, the group of degree-zero divisors supported on places of $F$ over $\overline{\mathbb{Q}}$ modulo the divisors of functions. The assertion is that there exists a $\overline{\mathbb{Q}}$-algebra automorphism $w$ of $F$, acting on $J_1(M)$ through the semilinear automorphism $(w,\mathrm{id})$, such that four laws hold. (1) For every prime $\ell$ and for every choice of the auxiliary data making the Hecke correspondence at $\ell$ available — integrality of the two degeneracy embeddings $\alpha$ (the inclusion) and $\beta$ (the $q\mapsto q^\ell$ map where defined, otherwise $\alpha$) of $F$ into the base-changed function field of $\Gamma_1(M)\cap\Gamma_0(M\ell)$, existence of principal divisors on that top field, the fundamental identity and the finiteness and pushforward norm formula along each of $\alpha$ and $\beta$ — one has $\beta_*\alpha^*(w\cdot x)=w\cdot\alpha_*\beta^*(x)$ for all $x\in J_1(M)$, where $\alpha_*\beta^*$ is `heckePic0OneBar` and $\beta_*\alpha^*$ is `heckePic0OneBarTranspose`. (2) For every $d\in\mathbb{N}$ and every $x$, $\langle d\rangle(w\cdot\langle d\rangle x)=w\cdot x$, where $\langle d\rangle=$ `diamondOneBar M d` is the $\mathbb{Z}$-linear endomorphism of $J_1(M)$ induced by the base change of the diamond automorphism. (3) $w\cdot(w\cdot x)=x$ for all $x$. (4) For every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ and every $c\in\mathbb{N}$ coprime to $M$ with $\sigma\zeta=\zeta^c$ for all $\zeta\in\overline{\mathbb{Q}}$ satisfying $\zeta^M=1$, and every $x$, one has $w\cdot(\sigma\cdot x)=\sigma\cdot\langle c\rangle(w\cdot x)$, the Galois action on $J_1(M)$ being the one on $q$-expansion coefficients.
--
--   This is the Atkin–Lehner–Li package for the Fricke involution $w_M$ at level $\Gamma_1(M)$: it transposes every Hecke correspondence $T_\ell$ (including $U_\ell$ for $\ell\mid M$), inverts the diamond operators, is an involution on $J_1(M)$, and twists the Galois action by a diamond operator according to the cyclotomic character on $\mu_M$. It is the level-$\Gamma_1(M)$ specialisation of the corresponding statement for the curves $X_H(M)$, and is used to produce the Galois-equivariant pairing on the Tate module of $J_1(M)$ for which the Hecke operators are self-adjoint up to the cyclotomic character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_frickeAlgEquiv_x1FunctionFieldBar_galois_smul (M : ℕ) [NeZero M] :
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
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (c : ℕ), c.Coprime M →
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ ^ c) → ∀ x : JOne M,
          SemilinearAut.ofAlgAut w • (σ • x)
            = σ • diamondOneBar M c (SemilinearAut.ofAlgAut w • x)) := by sorry
