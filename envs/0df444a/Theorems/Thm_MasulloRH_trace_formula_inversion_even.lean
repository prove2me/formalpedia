-- Prove2me | Theorems.Thm_MasulloRH_trace_formula_inversion_even
-- name    : MasulloRH.trace_formula_inversion_even
-- status  : Open
-- author  : @wojtek_politarczyk
-- created : 2026-11-22T12:16:03.847521+00:00
-- url     : https://prove2.me/theorems/e0ea93eb-d7f1-427a-bb98-390ca375f326
-- title:
--   Masullo trace formula restricted to inversion-even tests
-- statement:
--   Let $\alpha>0$ and let $\varphi:\mathbb R\to\mathbb C$ be smooth, compactly supported inside $(0,\infty)$, and zero at $1$. Assume additionally that it is even under inversion:
--
--   $$\varphi(t^{-1})=\varphi(t)\qquad(t>0).$$
--
--   Write $\Phi(s)=\int_0^\infty\varphi(t)t^{s-1}\,dt$, and let $Z_\alpha$ consist of the nontrivial zeros $\rho$ of the Riemann zeta function satisfying $|\operatorname{Re}\rho-1/2|<\alpha$, with $m_\rho$ their analytic multiplicities. The assertion is that the real integral is absolutely integrable, both displayed families are summable, and
--
--   $$
--   \int_1^\infty(\varphi(t)+\varphi(t^{-1}))\frac{\sqrt t}{t^2-1}\,dt
--   +\sum_{p\ {
--   m prime}}\sum_{n\ge1}\frac{\log p}{p^{n/2}}
--    (\varphi(p^n)+\varphi(p^{-n}))
--   =\Phi(1/2)+\Phi(-1/2)-\sum_{\rho\in Z_\alpha}m_\rho\Phi(\rho-1/2).
--   $$
--
--   This is an **open** restriction of the rational norm-invariant specialization of Masullo's proposed Theorem 12.5.1.1, not a proved trace identity. The positive window width is arbitrary; no height cutoff or exclusion of possible off-line zeros is introduced. The even/odd split is a supporting reduction, not a separate claim made in the manuscript. Together with the proved inversion-odd case and linearity, this subproblem suffices for the source-form frontier theorem. It retains the unresolved analytic content of that theorem; it does not establish RH.
--
--   **Formalization Note.** The test predicate, geometric terms and multiplicity-weighted spectral family are the existing `MasulloRH_RationalTrace` definitions. The prime-power sum uses the product index type, and the spectral sum is over distinct zero locations in the strict window.
-- source:
--   A. M. Masullo, The Music of the Primes, frozen 20 November 2026 draft, Theorem 12.5.1.1, pp.519–520, equations (12.5.1.1)–(12.5.1.3), https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . This is explicitly its inversion-even test restriction for F=Q. The symmetry reduction was proposed in sflicht's mission discussion https://prove2.me/missions/638f9b7f-e232-4624-ba08-5889465bb1e7#comment-1029cf02-5987-433d-bd01-6c510b4884b7 ; the proved odd case is https://prove2.me/theorems/2670a1dc-66aa-4dd0-b532-6dde62e0f3de .

import Definitions.Def_MasulloRH_RationalTrace
open MasulloRH MeasureTheory Set
set_option autoImplicit false

theorem MasulloRH.trace_formula_inversion_even (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (heven : ∀ t : ℝ, 0 < t → φ t⁻¹ = φ t) :
    IntegrableOn (realTraceIntegrand φ) (Ioi 1) ∧
    Summable (primePowerTraceTerm φ) ∧ Summable (zetaTraceTerm φ α) ∧
    (∫ t in Ioi (1 : ℝ), realTraceIntegrand φ t) +
      (∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by sorry
