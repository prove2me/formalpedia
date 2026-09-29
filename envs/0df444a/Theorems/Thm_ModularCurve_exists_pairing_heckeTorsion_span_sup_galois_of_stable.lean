-- Prove2me | Theorems.Thm_ModularCurve_exists_pairing_heckeTorsion_span_sup_galois_of_stable
-- name    : ModularCurve.exists_pairing_heckeTorsion_span_sup_galois_of_stable
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/62ad9442-2806-551f-a4ad-876c33506865
-- title:
--   Galois-equivariant pairing on stable Eisenstein torsion of J₀(p)
-- statement:
--   Let $p$ and $q$ be primes with $q\ne p$, and give the degree-zero divisor class group `JZero p` — the quotient of the degree-zero divisors by the principal divisors for the base change to $\overline{\mathbf Q}$ of the function field of level $p$ — its module structure over `HeckeAlg` $=\mathbf Z[X_\ell:\ell\text{ prime}]$ supplied by `heckeModuleBar p`. Write $\mathfrak P=$ `eisensteinMaximalIdeal p q` for the preimage under the evaluation `eisensteinEval p` of the ideal $(q)\subset\mathbf Z$, and for $k,M\in\mathbf N$ let $V_M$ be the submodule of elements annihilated by every element of $(q^k)+\mathfrak P^M$. The assertion is: for all $k$ and $M$, if $V_{M+1}=V_M$, then there is a function $B:$ `JZero p` $\times$ `JZero p` $\to\overline{\mathbf Q}$ such that for all $x,x',y,y'\in V_M$ one has $B(x,y)^{q^k}=1$, $B(x+x',y)=B(x,y)B(x',y)$, $B(x,y+y')=B(x,y)B(x,y')$, the implication that $B(x,y)=1$ for all $y\in V_M$ forces $x=0$, and $B(\sigma\cdot x,\sigma\cdot y)=\sigma(B(x,y))$ for every $\sigma\in\operatorname{Aut}_{\mathbf Q}(\overline{\mathbf Q})$ acting on `JZero p`.
--
--   This is the existence, on the $\mathfrak P$-primary part of the $q^k$-torsion of the Jacobian at a stable exponent $M$, of a $\mu_{q^k}$-valued Galois-equivariant pairing that is nondegenerate in the first variable — the restriction of the Fricke-twisted Weil pairing in Mazur's study of the Eisenstein ideal. It feeds the comparison of the order of a quotient of the Hecke lattice algebra with the order of the image of the Eisenstein torsion under reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pairing_heckeTorsion_span_sup_galois_of_stable.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_EisensteinIdeal

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_pairing_heckeTorsion_span_sup_galois_of_stable
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (hqp : q ≠ p) :
    letI := heckeModuleBar p
    ∀ k M : ℕ,
      heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ (M + 1)) =
        heckeTorsion (JZero p)
          (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M) →
      ∃ B : JZero p → JZero p → AlgebraicClosure ℚ,
        (∀ x ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ y ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          B x y ^ (q ^ k) = 1) ∧
        (∀ x ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ x' ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ y ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          B (x + x') y = B x y * B x' y) ∧
        (∀ x ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ y ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ y' ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          B x (y + y') = B x y * B x y') ∧
        (∀ x ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          (∀ y ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
            B x y = 1) → x = 0) ∧
        (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
         ∀ x ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
         ∀ y ∈ heckeTorsion (JZero p) (Ideal.span {((q : ℕ) ^ k : HeckeAlg)} ⊔ (eisensteinMaximalIdeal p q) ^ M),
          B (σ • x) (σ • y) = σ (B x y)) := by sorry
