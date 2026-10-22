-- Prove2me | Theorems.Thm_NatureSLT_IllPosed_approximate_operator
-- name    : NatureSLT.IllPosed.approximate_operator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-20T15:52:51.85872+00:00
-- url     : https://prove2.me/theorems/c3e413e1-2f27-4c72-a4ae-6fccb9fe2a3b
-- title:
--   Theorem 7.5 — Tikhonov regularization with approximately defined operator and right-hand side, (7.49)
-- statement:
--   Let $E_1, E_2$ be metric spaces (with Borel $\sigma$-algebras), $A : E_1 \to E_2$ a continuous one-to-one map, $\Omega$ a regularization functional on $E_1$ (lower semicontinuous, values in $[0,\infty]$, compact sets $\{\Omega \le c\}$ for $c > 0$), and $f$ with $\Omega(f) < \infty$ a solution of $A f = F$. For two maps $B, A$ write $\|B - A\| = \sup_{\Omega(g) < \infty} \rho_{E_2}(Bg, Ag)/\Omega^{1/2}(g)$ (7.48).
--
--   Then for any $\varepsilon > 0$ and any constants $C_1, C_2 > 0$ there is $\gamma_0 > 0$ with the following property. Let $0 < \gamma \le \gamma_0$, and on a probability space $(S, P)$ let $F'$ be a random element of $E_2$ (the approximate right-hand side), $A'$ a random continuous operator $E_1 \to E_2$ (the approximate operator), and $f'$ a random element of $E_1$ that, for every outcome, minimizes $W(g) = \rho^2_{E_2}(A' g, F') + \gamma\, \Omega(g)$ over $E_1$. Then
--
--   $$P\{\rho_{E_1}(f', f) > \varepsilon\} \le P\{\rho_{E_2}(F', F) > C_1 \sqrt{\gamma}\} + P\{\|A' - A\| > C_2 \sqrt{\gamma}\}. \tag{7.49}$$
--
--   In the book $F' = F_\ell$, $A' = A_\ell$, $f' = f_\ell$ and $\gamma = \gamma_\ell$ form a sequence; the theorem lets one prove consistency of Method T when both the data and the operator are estimated, as in conditional probability estimation (§7.9).
--
--   **Formalization Note** $\gamma_0$ depends only on $\varepsilon$, $C_1$, $C_2$ and the fixed objects $A$, $F$, $f$, $\Omega$, $(S,P)$, and the inequality is required for every admissible random data at every level $0 < \gamma \le \gamma_0$; this is the book's "for any $\gamma_\ell \le \gamma_0$" with the sequence index removed. $F'$, $f'$ and the random distance $\|A' - A\|$ are assumed measurable. The distance (7.48) is computed in $[0,\infty]$ over the domain of $\Omega$; at points with $\Omega(g) = 0$ the quotient is $0$ if $A'g = Ag$ and $\infty$ otherwise. The exact solution is assumed to lie in the domain of $\Omega$.
-- source:
--   Vapnik, The Nature of Statistical Learning Theory, 2nd ed., Springer 2000, p. 251, Theorem 7.5

import Mathlib
import Definitions.Def_NatureSLT_IllPosed_IsRegularizer
import Definitions.Def_NatureSLT_IllPosed_tikhonovFunctional
import Definitions.Def_NatureSLT_IllPosed_operatorDistance

namespace NatureSLT.IllPosed

open Filter Topology MeasureTheory
open scoped ENNReal

/-- Theorem 7.5 (Vapnik, *The Nature of Statistical Learning Theory*, 2nd ed., §7.9.1, p. 251;
Stefanyuk 1986). Setting of §7.9.1: `A : E₁ → E₂` is a continuous one-to-one map between metric
spaces, `Ω` a regularization functional (p. 235), `f` an exact solution of `A f = F` in the domain
`{Ω < ∞}`. Instead of `F` and `A` one is given a random right-hand side `F' : S → E₂` and a random
continuous operator `A' : S → (E₁ → E₂)` on a probability space `(S, P)`, at distance
`‖A' − A‖` of (7.48), and `f'(ω)` minimizes `W(g) = ρ²_{E₂}(A'(ω) g, F'(ω)) + γ Ω(g)`, with
`F'`, `f'` and `ω ↦ ‖A'(ω) − A‖` measurable. Then for any `ε > 0` and any constants
`C₁, C₂ > 0` there is `γ₀ > 0` such that for any `0 < γ ≤ γ₀` (and any such random data)
`P{ρ_{E₁}(f', f) > ε} ≤ P{ρ_{E₂}(F', F) > C₁ √γ} + P{‖A' − A‖ > C₂ √γ}` (7.49). -/
theorem approximate_operator {E₁ E₂ S : Type*}
    [MetricSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
    [MetricSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
    [MeasurableSpace S] (P : Measure S) [IsProbabilityMeasure P]
    (A : E₁ → E₂) (hA : Continuous A) (hAinj : Function.Injective A)
    (Ω : E₁ → ℝ≥0∞) (hΩ : IsRegularizer Ω)
    (F : E₂) (f : E₁) (hf : A f = F) (hfΩ : Ω f ≠ ⊤) :
    ∀ ε : ℝ, 0 < ε → ∀ C₁ C₂ : ℝ, 0 < C₁ → 0 < C₂ → ∃ γ₀ : ℝ, 0 < γ₀ ∧
      ∀ γ : ℝ, 0 < γ → γ ≤ γ₀ →
      ∀ (F' : S → E₂) (A' : S → E₁ → E₂) (f' : S → E₁),
        Measurable F' → (∀ ω, Continuous (A' ω)) →
        Measurable (fun ω => operatorDistance (A' ω) A Ω) → Measurable f' →
        (∀ (ω : S) (g : E₁),
          tikhonovFunctional (A' ω) Ω γ (F' ω) (f' ω) ≤ tikhonovFunctional (A' ω) Ω γ (F' ω) g) →
        P {ω | ε < dist (f' ω) f} ≤
          P {ω | C₁ * Real.sqrt γ < dist (F' ω) F} +
            P {ω | ENNReal.ofReal (C₂ * Real.sqrt γ) < operatorDistance (A' ω) A Ω} := by sorry

end NatureSLT.IllPosed
