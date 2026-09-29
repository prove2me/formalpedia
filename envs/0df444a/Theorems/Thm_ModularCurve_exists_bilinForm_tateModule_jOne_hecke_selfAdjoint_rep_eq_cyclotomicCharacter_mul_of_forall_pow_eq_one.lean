-- Prove2me | Theorems.Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
-- name    : ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c48f0ef0-78be-51a0-8c43-2b98e6abbdaf
-- title:
--   Fricke-twisted p-adic Weil pairing on TₚJ₁(M)⊗ K
-- statement:
--   Fix a natural number $M \neq 0$ and a prime $p$, and let $K$ be a field of characteristic zero equipped with a $\mathbb{Z}_p$-algebra structure. Write $J =$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) for the group $\mathrm{Pic}^0$ of degree-zero divisor classes of the base change to $\overline{\mathbb{Q}}$ of the function field of $X_1(M)$ in its Laurent-series ($q$-expansion) model, carrying the coefficientwise action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \overline{\mathbb{Q}} \simeq_{\mathbb{Q}}^{\mathrm{alg}} \overline{\mathbb{Q}}$, and give $J$ the module structure [`ModularCurve.heckeModuleOneBar M`](def/ModularCurve_X1HeckeModule.html#L129) over [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16), the polynomial ring $\mathbb{Z}[x_i]$ on generators indexed by $\mathrm{Primes} \sqcup \mathbb{N}$, obtained by evaluating the generators at the Hecke and diamond endomorphisms of $J$ when these commute and at $0$ otherwise. Let $T =$ [`TateModule p J`](def/EllipticCurve_TateModule.html#L15) be the $\mathbb{Z}_p$-module of sequences $(x_n)_{n \in \mathbb{N}}$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$, and put $V = K \otimes_{\mathbb{Z}_p} T$. The assertion is that there exists a $K$-bilinear form $B$ on $V$ such that: (i) $B(v,w)=0$ for all $w$ forces $v=0$, and $B(v,w)=0$ for all $v$ forces $w=0$; (ii) for every $t \in$ [`ModularCurve.HeckeAlgOne`](def/ModularCurve_X1HeckeModule.html#L16), the base change to $K$ of the induced endomorphism [`ModularCurve.tateHeckeRepOne p J t`](def/ModularCurve_X1HeckeModule.html#L176) of $T$ is self-adjoint for $B$; and (iii) for every $\sigma \in \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ fixing every $\zeta \in \overline{\mathbb{Q}}$ with $\zeta^M = 1$, one has $B(\sigma v, \sigma w) = \chi_p(\sigma)\,B(v,w)$ for all $v,w \in V$, where $\sigma$ acts by the base change of [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) and $\chi_p(\sigma) \in \mathbb{Z}_p^\times$ is the value of the $p$-adic cyclotomic character, read in $K$ through $\mathbb{Z}_p \to K$. Note that the Galois scaling law (iii) is asserted only for $\sigma$ fixing all $M$-th roots of unity, and not in a form involving a diamond twist.
--
--   Classically the form $B$ is the base change to $K$ of the $p$-adic Weil pairing on $T_pJ_1(M)$ twisted by the Fricke involution $w_M$, for which the covariant Hecke and diamond operators become self-adjoint (the Rosati involution being conjugation by $w_M$) and which scales by the cyclotomic character. It supplies the pairing used in the study of the Frobenius action on quotients of the Tate module of $J_1(M)$ at primes dividing the level exactly once.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped TensorProduct

theorem ModularCurve.exists_bilinForm_tateModule_jOne_hecke_selfAdjoint_rep_eq_cyclotomicCharacter_mul_of_forall_pow_eq_one
    (M p : ℕ) [NeZero M] [Fact p.Prime]
    (K : Type) [Field K] [CharZero K] [Algebra ℤ_[p] K] :
    letI := ModularCurve.heckeModuleOneBar M
    ∃ B : LinearMap.BilinForm K (K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
      (∀ v, (∀ w, B v w = 0) → v = 0) ∧ (∀ w, (∀ v, B v w = 0) → w = 0) ∧
      (∀ (t : ModularCurve.HeckeAlgOne) (v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M)),
        B ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K v) w =
          B v ((ModularCurve.tateHeckeRepOne p (ModularCurve.JOne M) t).baseChange K w)) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ ζ : AlgebraicClosure ℚ, ζ ^ M = 1 → σ ζ = ζ) →
        ∀ v w : K ⊗[ℤ_[p]] TateModule p (ModularCurve.JOne M),
          B ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K v)
            ((TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ).baseChange
                K w) =
            algebraMap ℤ_[p] K
                ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) * B v w := by sorry
