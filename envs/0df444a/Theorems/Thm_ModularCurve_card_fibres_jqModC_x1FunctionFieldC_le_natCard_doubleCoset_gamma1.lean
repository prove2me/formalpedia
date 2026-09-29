-- Prove2me | Theorems.Thm_ModularCurve_card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1
-- name    : ModularCurve.card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/3019ab84-309f-5806-8553-1843aaf04fe8
-- title:
--   Characteristic-ℓ fibre counts over j=0,1728,∞ for Γ₁(M)
-- statement:
--   Let $M$ be a nonzero natural number, let $\ell$ be a prime not dividing $M$, and let $K$ be an algebraically closed field of characteristic $\ell$. Write $K_0 =$ [`ModularCurve.x1FunctionFieldC K M`](def/ModularCurve_X1.html#L134) for the intermediate field of the Laurent series field $K((q))$ obtained by adjoining to $K$ the set of integral form ratios `intFormRatiosC K (Gamma1 M)`. Let $x \in K_0$ be an element whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), namely $q^{-1}$ times the image in $K$ of the power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum`. Places of $K_0$ over $K$ are valuation subrings of $K_0$ containing the image of $K$, distinct from $K_0$ itself and principal ideal rings, with $\operatorname{ord}$ the negative of the logarithm of the associated adic valuation. Let $S_0, S_1, S_\infty$ be finite sets of such places, characterised by: $Q \in S_0$ iff $\operatorname{ord}_Q x > 0$; $Q \in S_1$ iff $\operatorname{ord}_Q(x - 1728) > 0$; $Q \in S_\infty$ iff $\operatorname{ord}_Q x < 0$. Then $|S_0|$, $|S_1|$ and $|S_\infty|$ are bounded above by the cardinalities of the double coset spaces $\Gamma_1(M) \backslash \mathrm{SL}_2(\mathbb Z) / \langle ST \rangle$, $\Gamma_1(M) \backslash \mathrm{SL}_2(\mathbb Z) / \langle S \rangle$ and $\Gamma_1(M) \backslash \mathrm{SL}_2(\mathbb Z) / \langle T, -1 \rangle$ respectively.
--
--   This is the $\Gamma_1(M)$ case of the characteristic-$\ell$ count of places of the $q$-expansion function field lying over the three distinguished values $j = 0$, $j = 1728$ and $j = \infty$, the bounds being the corresponding numbers of elliptic and cusp orbits in the classical $\Gamma_H$-picture. It is stated separately so that consumers typed on the $X_1(M)$ function field can use it directly; it is cited in the computation of $\operatorname{ord}_Q(x - c)$ in terms of the ramification width at places of `x1FunctionFieldC`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CongruenceSubgroup AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.card_fibres_jqModC_x1FunctionFieldC_le_natCard_doubleCoset_gamma1
    (M : ℕ) [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (x : ModularCurve.x1FunctionFieldC K M)
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (S₀ S₁ Sinf : Finset (AlgebraicCurve.Place K (ModularCurve.x1FunctionFieldC K M)))
    (hS₀ : ∀ Q, Q ∈ S₀ ↔ 0 < Q.ord x) (hS₁ : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728))
    (hSinf : ∀ Q, Q ∈ Sinf ↔ Q.ord x < 0) :
    S₀.card ≤ Nat.card (DoubleCoset.Quotient
        (CongruenceSubgroup.Gamma1 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      S₁.card ≤ Nat.card (DoubleCoset.Quotient
        (CongruenceSubgroup.Gamma1 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      Sinf.card ≤ Nat.card (DoubleCoset.Quotient
        (CongruenceSubgroup.Gamma1 M : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
            Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by sorry
