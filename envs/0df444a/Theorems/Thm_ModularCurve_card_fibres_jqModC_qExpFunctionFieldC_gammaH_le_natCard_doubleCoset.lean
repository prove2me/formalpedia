-- Prove2me | Theorems.Thm_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
-- name    : ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/8ae656d6-6ccb-558b-9c20-57ba13b2ee4e
-- title:
--   Bounding fibres of j over 0, 1728, ∞ in characteristic ℓ
-- statement:
--   Fix $M \geq 1$ and a subgroup $H \leq (\mathbb{Z}/M)^\times$, and let $\Gamma_H(M) \leq \mathrm{SL}(2,\mathbb{Z})$ be the image under the inclusion of $\Gamma_0(M)$ of the preimage of $H$ under the character of $\Gamma_0(M)$ sending $\gamma$ to the unit of $\mathbb{Z}/M$ represented by its lower-right entry. Let $\ell$ be a prime with $\ell \nmid M$ and let $K$ be an algebraically closed field of characteristic $\ell$. Let $F =$ [`ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H)`](def/ModularCurve_X1.html#L101) be the subfield of $K((q))$ generated over $K$ by the quotients $\bar p_f/\bar p_g$ of coefficientwise reductions to $K$ of integral $q$-expansions $p_f, p_g$ of two modular forms of equal weight on $\Gamma_H(M)$, with $\bar p_g \neq 0$. Let $x \in F$ be an element whose underlying Laurent series is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15), the reduction to $K$ of $q^{-1} \cdot (E_4^3 \eta^{-24})$, i.e. of the $q$-expansion of $j$. Let $S_0$, $S_1$, $S_\infty$ be finite sets of places of $F$ over $K$ (valuation subrings of $F$ containing $K$, proper and with principal ideals) characterised by $\operatorname{ord}_Q x > 0$, $\operatorname{ord}_Q(x - 1728) > 0$ and $\operatorname{ord}_Q x < 0$ respectively, where $\operatorname{ord}$ is the normalised additive valuation attached to the place. Then $|S_0| \leq \#\big(\Gamma_H(M) \backslash \mathrm{SL}(2,\mathbb{Z}) / \langle ST\rangle\big)$, $|S_1| \leq \#\big(\Gamma_H(M) \backslash \mathrm{SL}(2,\mathbb{Z}) / \langle S\rangle\big)$ and $|S_\infty| \leq \#\big(\Gamma_H(M) \backslash \mathrm{SL}(2,\mathbb{Z}) / \langle T, -1\rangle\big)$, the right-hand sides being the cardinalities of the corresponding double-coset quotients, with $S = \begin{pmatrix} 0 & -1 \\ 1 & 0\end{pmatrix}$ and $T = \begin{pmatrix} 1 & 1 \\ 0 & 1\end{pmatrix}$.
--
--   This is the counting half of Igusa's comparison between $X_H(M)$ in characteristic $0$ and its reduction modulo a prime $\ell$ not dividing the level: the fibres over the three distinguished points $j = 0$, $j = 1728$, $j = \infty$ of the reduced covering of the $j$-line have at most as many points as the corresponding fibres in characteristic $0$, whose cardinalities are the three double-coset numbers $\Gamma_H(M)\backslash \mathrm{SL}(2,\mathbb{Z})/\langle ST\rangle$, $\langle S\rangle$ and $\langle T,-1\rangle$. It feeds the corresponding statement for the function field of $X_1(M)$ and the comparison of genera of $X_H(M)$ in characteristic $\ell$ and in characteristic $0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset.lean

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped MatrixGroups

set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.card_fibres_jqModC_qExpFunctionFieldC_gammaH_le_natCard_doubleCoset
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K ℓ]
    (x : ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))
    (hx : (x : LaurentSeries K) = ModularCurve.jqModC K)
    (S₀ S₁ Sinf : Finset (AlgebraicCurve.Place K (ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH M H))))
    (hS₀ : ∀ Q, Q ∈ S₀ ↔ 0 < Q.ord x) (hS₁ : ∀ Q, Q ∈ S₁ ↔ 0 < Q.ord (x - 1728))
    (hSinf : ∀ Q, Q ∈ Sinf ↔ Q.ord x < 0) :
    S₀.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      S₁.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        (Subgroup.zpowers ModularGroup.S : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) ∧
      Sinf.card ≤ Nat.card (DoubleCoset.Quotient
        (CohCarrier.GammaH M H : Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) :
            Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) :
          Set (Matrix.SpecialLinearGroup (Fin 2) ℤ))) := by sorry
