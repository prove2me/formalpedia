-- Prove2me | Theorems.Thm_ModularCurve_exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
-- name    : ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c0145cd0-f141-575b-a4ec-a04ebc5995b3
-- title:
--   The β-fibre over a cusp: ramification 1 and ℓ
-- statement:
--   Fix natural numbers $N \neq 0$ and $\ell$ with $\ell$ prime and $\ell \nmid N$. Assume that the two degeneracy maps at level $\ell$ are integral: `HeckeAlphaBarIntegral` for `heckeAlphaBar`, the inclusion of $\bar{\mathbb{Q}}$-algebras $\mathrm{laurentBaseChange}\,\bar{\mathbb{Q}}\,(\mathrm{modularFunctionFieldFull}\,N) \to \mathrm{laurentBaseChange}\,\bar{\mathbb{Q}}\,(\mathrm{modularFunctionFieldFull}\,(N\ell))$, and `HeckeBetaBarIntegral` for `heckeBetaBar`, the map induced on these fields by the substitution $q \mapsto q^{\ell}$ on Laurent series. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\bar{\mathbb{Q}}$ with $\sigma\zeta = \zeta^{\ell}$ for every $\zeta$ satisfying $\zeta^{N} = 1$. Let $v$ be a place of $\mathrm{modularFunctionFieldBar}\,N$ over $\bar{\mathbb{Q}}$ — a proper valuation subring containing the image of $\bar{\mathbb{Q}}$ and a principal ideal ring — at which the element `jq` (the $q$-expansion $q^{-1}\cdot\,$(power series) of the modular invariant, transported by `coeffEmb` to coefficients in $\bar{\mathbb{Q}}$) has $\mathrm{ord}\,<0$, i.e. a pole; so $v$ is a cusp. Then there exist places $W_1, W_2$ of $\mathrm{laurentBaseChange}\,\bar{\mathbb{Q}}\,(\mathrm{modularFunctionFieldFull}\,(N\ell))$ whose restrictions along `heckeBetaBar` both equal $v$, with ramification indices along `heckeBetaBar` equal to $1$ and to $\ell$ respectively, such that the restriction of $W_1$ along `heckeAlphaBar` is $\mathrm{arithmeticGalois}\,\sigma \cdot v$, while $\mathrm{arithmeticGalois}\,\sigma$ carries the restriction of $W_2$ along `heckeAlphaBar` to $v$, where `arithmeticGalois` is the semilinear action of $\sigma$ on places obtained by letting $\sigma$ act on Laurent coefficients.
--
--   This is the behaviour of the Hecke correspondence $T_\ell = \alpha_* \beta^*$ at the cusps of the geometric level-$N$ modular curve, read at the grain of places of function fields: over a cusp the $\beta$-fibre contains an unramified place whose $\alpha$-image is the $\sigma$-conjugate cusp and a place of ramification index $\ell$ whose $\alpha$-image is carried to the cusp by $\sigma$, the twist reflecting the action of $\mathrm{Gal}(\bar{\mathbb{Q}}/\mathbb{Q})$ on cusps through the cyclotomic character modulo $N$. It feeds the prolongation-tuple lemmas that sum ramification indices along `heckeAlphaBar` over the $\beta$-fibre and identify the Frobenius behaviour on the places lying on the infinity side.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pair_fiberAlong_heckeBetaBar_of_ord_neg.lean

import Definitions.Def_ModularCurve_HeckeOperator

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_pair_fiberAlong_heckeBetaBar_of_ord_neg
    (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] (hlN : ¬ ℓ ∣ N)
    (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (hσ : ∀ ζ : AlgebraicClosure ℚ, ζ ^ N = 1 → σ ζ = ζ ^ ℓ)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hcusp : v.ord
        (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
              (modularFunctionField_le_full N (jq_mem N))⟩ : modularFunctionFieldBar N) < 0) :
    ∃ W₁ W₂ : Place (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ))),
      W₁.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v
        ∧ W₂.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) hβ = v
        ∧ W₁.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = 1
        ∧ W₂.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) N ℓ) = ℓ
        ∧ W₁.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα
            = arithmeticGalois (modularFunctionFieldFull N) σ • v
        ∧ arithmeticGalois (modularFunctionFieldFull N) σ
              • (W₂.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hα) = v := by sorry
