-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero
-- name    : ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/10a8535e-aaea-506b-b133-07bb1902183c
-- title:
--   Coset representatives give roots of Φ_N(j(τ),·)
-- statement:
--   Let $N$ be a nonzero natural number and let `data` be a datum of type [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), i.e. a two-variable integral polynomial $\Phi =$ `data.Φ` in `Polynomial (Polynomial ℤ)` which is monic in the outer variable, whose degree in that variable equals `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies the formal relation `Φ.eval₂ evalAtJ (jqN N) = 0` in Laurent series over $\mathbb{Q}$, where the coefficient polynomials are evaluated at the $q$-expansion of $j$ and the outer variable at `jqN N`. Let $(a,b,d)$ be a triple of natural numbers lying in [`ModularCurve.primCosetReps N`](def/ModularCurve_PrimCosetReps.html#L8), that is, $a, b, d \le N$ with $a d = N$, $b < d$ and $\gcd(a, \gcd(b,d)) = 1$. Let $\tau, \tau'$ be points of the upper half-plane whose complex coordinates satisfy $\tau' = (a\tau + b)/d$. Writing $j(z) = E_4(z)^3/\Delta(z)$ for the quotient of the Eisenstein series `ModularForm.E₄` cubed by `ModularForm.discriminant`, the conclusion is that the complex polynomial obtained from $\Phi$ by mapping each integral coefficient polynomial to its value at $j(\tau)$ under $\mathbb{Z} \to \mathbb{C}$ vanishes at $j(\tau')$; in classical notation, $\Phi_N\bigl(j(\tau), j\bigl(\tfrac{a\tau+b}{d}\bigr)\bigr) = 0$.
--
--   This is the analytic statement that every function $\tau \mapsto j((a\tau+b)/d)$ attached to a primitive coset representative of level $N$ is a root of $\Phi_N(j(\tau), Y)$, the classical first assertion about the modular equation. It supplies the input, not available from the single formal identity $\Phi_N(j(q), j(q^N)) = 0$ at composite $N$, used in the construction of coset root data for $X_0(N)$ and in the vanishing of $\Phi_N$ on cyclic isogenies of complex tori.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_eval_E4_cube_div_discriminant_coset_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open UpperHalfPlane

theorem ModularCurve.ModularPolynomialData.eval_E4_cube_div_discriminant_coset_eq_zero (N : ℕ) [NeZero N]
    (data : ModularCurve.ModularPolynomialData N) {a b d : ℕ} (habd : (a, b, d) ∈ ModularCurve.primCosetReps N)
    (τ τ' : ℍ) (hτ' : (τ' : ℂ) = ((a : ℂ) * τ + b) / d) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
        ((ModularForm.E₄ : ℍ → ℂ) τ ^ 3 / ModularForm.discriminant τ))).eval
      ((ModularForm.E₄ : ℍ → ℂ) τ' ^ 3 / ModularForm.discriminant τ') = 0 := by sorry
