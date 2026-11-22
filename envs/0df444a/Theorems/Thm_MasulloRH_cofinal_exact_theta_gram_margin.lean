-- Prove2me | Theorems.Thm_MasulloRH_cofinal_exact_theta_gram_margin
-- name    : MasulloRH.cofinal_exact_theta_gram_margin
-- status  : Open
-- author  : @sflicht
-- created : 2026-11-21T15:01:29.622772+00:00
-- url     : https://prove2.me/theorems/b2ce922d-3f53-4192-b8a7-484fcd931614
-- title:
--   Exact strict theta Gram margins at arbitrarily large scales
-- statement:
--   Use the functions $\theta$ and $\operatorname{pulse}$ from `MasulloRH.GaussianApproximation`, as defined in `Definitions.Def_MasulloRH_GaussianThetaApproximation`. For every natural number $N$, there exist a natural number $n\ge N$, a finite number $m$ of translates, rational complex coefficients $a_i\in\mathbb Q+\mathrm{i}\mathbb Q$, and rational shifts $y_i\in\mathbb Q$ with the following property.
--
--   Set
--
--   $$
--   \delta_n=\frac{1}{16(n+1)},\qquad
--   u_0(x)=\operatorname{pulse}(n,x),\quad d_0=1,\qquad
--   u_{i+1}(x)=\theta(x-y_i),\quad d_{i+1}=-a_i\quad(0\le i<m),
--   $$
--
--   and form the exact finite matrix
--
--   $$
--   G_{ij}=\int_{\mathbb R}
--   \exp\!\left(\frac32x+2\left(\frac14-\delta_n\right)|x|\right)
--   \overline{u_i(x)}u_j(x)\,dx
--   \qquad(0\le i,j\le m).
--   $$
--
--   The asserted strict margin is
--
--   $$
--   \operatorname{Re}\sum_{i,j=0}^{m}\overline{d_i}d_jG_{ij}<\frac{\delta_n}{2}.
--   $$
--
--   This is an open exact-margin formulation supporting `MasulloRH.cofinal_rational_theta_gram_interval_tables`. It retains the same cofinal quantifier, rational coefficients, rational shifts, matrix entries, and threshold, while omitting the rational approximating matrix and its error bound. The finite rounding lemma supplies those additional witnesses once this strict margin is established.
--
--   **Formalization Note.** The displayed integrals are the exact complex integrals in the existing Lean definitions; the assertion adds no separate integrability conclusion. Rational complex coefficients are represented by pairs of rationals.
-- source:
--   New exact-margin supporting formulation of MasulloRH.cofinal_rational_theta_gram_interval_tables, https://prove2.me/theorems/7f59c68d-29e6-404c-a754-27288c412b6c , using its identical cofinality quantifier, rational coefficient/shift witnesses, theta/pulse Gram entries and delta/2 threshold; rational matrix/error witnesses are removed. Functions are from Definitions.Def_MasulloRH_GaussianThetaApproximation (definition 6f34c003-4870-4c6a-b83e-256b289a15db). This is a new open reformulation supporting the mission, not an assertion that the strict Gram margin has been proved in Masullo, The Music of the Primes.

import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH.GaussianApproximation MeasureTheory
open scoped BigOperators ComplexConjugate
set_option autoImplicit false

theorem MasulloRH.cofinal_exact_theta_gram_margin :
    ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (m : ℕ) (a : Fin m → ℚ × ℚ) (y : Fin m → ℚ),
        let δ : ℝ := 1 / (16 * ((n : ℝ) + 1))
        let u : Fin (m + 1) → ℝ → ℂ := Fin.cons (pulse n)
          (fun i x => theta (x - (y i : ℝ)))
        let d : Fin (m + 1) → ℂ := Fin.cons 1
          (fun i => -(((a i).1 : ℂ) + ((a i).2 : ℂ) * Complex.I))
        (∑ i, ∑ j, conj (d i) * d j *
          (∫ x : ℝ,
            (Real.exp (2 * (3 / 4) * x + 2 * (1 / 4 - δ) * |x|) : ℂ) *
              conj (u i x) * u j x)).re < δ / 2 := by sorry
