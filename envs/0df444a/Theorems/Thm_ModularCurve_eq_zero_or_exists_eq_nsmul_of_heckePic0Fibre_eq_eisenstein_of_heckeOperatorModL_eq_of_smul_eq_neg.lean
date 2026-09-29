-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
-- name    : ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/5e946126-0962-58b7-8839-af0f6a5593f4
-- title:
--   Cyclicity of Eisenstein classes on the characteristic-q fibre
-- statement:
--   Let $k$ be an algebraically closed field of characteristic a prime $q$, and let $p$ be a prime with $p \neq 0$ in $k$. Write $F =$ `modularFunctionFieldC k p` for the intermediate field of the Laurent series field $k((\mathfrak q))$ generated over $k$ by the two series `jqModC k` and `jqNModC k p`, and assume it coincides with `modularFunctionFieldFullC k p`, the subfield generated over $k$ by the family `divisorExpansionsC k p`. Let $\tau$ be a $k$-algebra automorphism of $F$ interchanging the generators `jqModC k` and `jqNModC k p`. Let $Z$ be an additive subgroup of $\mathrm{Pic}^0(F/k)$, the quotient of the degree-zero divisors (finitely supported $\mathbb Z$-valued functions on the places `Place k F`) by the principal ones, such that every $z \in Z$ satisfies: $q \cdot z = 0$; $(\mathrm{heckePic0Fibre}\ k\ p\ \ell)(z) = (\ell+1)\cdot z$ for every prime $\ell \neq p$ with $\ell \neq 0$ in $k$; $(\mathrm{heckePic0Fibre}\ k\ p\ p)(z) = z$; $\tau \cdot z = -z$; and the image of $z$ under the transport of $\mathrm{Pic}^0$ along the equality of fields is fixed by `heckeOperatorModL k p q`, the sum of `frobeniusPushforwardModL` and `frobeniusPullbackModL` at $q$. Then for all $z_1, z_2 \in Z$, either $z_1 = 0$ or $z_2 = m \cdot z_1$ for some natural number $m$.
--
--   This is the multiplicity-one, or cyclicity, statement for the subgroup of $q$-torsion classes on the characteristic-$q$ fibre of $X_0(p)$ that are Eisenstein for the Hecke operators away from $p$, fixed by the operator at $p$, anti-fixed by the involution exchanging the two $j$-expansions, and fixed by the sum of Frobenius pushforward and pullback; unlike Mazur's setting, the sign of the Fricke action is imposed as a hypothesis rather than deduced. It feeds the construction of a single generator for the relevant Hecke-torsion subgroup in [`ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero`](thm.html#ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_HeckeOperatorModL
import Definitions.Def_AlgebraicCurve_Pic0Congr

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem ModularCurve.eq_zero_or_exists_eq_nsmul_of_heckePic0Fibre_eq_eisenstein_of_heckeOperatorModL_eq_of_smul_eq_neg
    (k : Type*) [Field k] [IsAlgClosed k] (q : ℕ) [Fact q.Prime] [CharP k q]
    (p : ℕ) [Fact p.Prime] (hp : (p : k) ≠ 0)
    (hE : modularFunctionFieldC k p = modularFunctionFieldFullC k p)
    (τ : modularFunctionFieldC k p ≃ₐ[k] modularFunctionFieldC k p)
    (hτ₁ : τ ⟨jqModC k, jqModC_mem k p⟩ = ⟨jqNModC k p, jqNModC_mem k p⟩)
    (hτ₂ : τ ⟨jqNModC k p, jqNModC_mem k p⟩ = ⟨jqModC k, jqModC_mem k p⟩)
    (Z : AddSubgroup (Pic0 k (modularFunctionFieldC k p)))
    (hq : ∀ z ∈ Z, (q : ℤ) • z = 0)
    (hT : ∀ z ∈ Z, ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ p → ((ℓ : ℕ) : k) ≠ 0 →
      (letI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩; heckePic0Fibre k p ℓ z) = (((ℓ : ℕ) + 1 : ℕ) : ℤ) • z)
    (hU : ∀ z ∈ Z, heckePic0Fibre k p p z = z)
    (hW : ∀ z ∈ Z, τ • z = -z)
    (hF : ∀ z ∈ Z,
      heckeOperatorModL k p q
          (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a) z) =
        Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
          (fun a => (IntermediateField.equivOfEq hE).commutes a) z) :
    ∀ z₁ ∈ Z, ∀ z₂ ∈ Z, z₁ = 0 ∨ ∃ m : ℕ, z₂ = m • z₁ := by sorry
