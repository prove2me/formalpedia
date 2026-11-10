-- Prove2me | Theorems.Thm_HoneycombCodes_lemma_6_2
-- name    : HoneycombCodes.lemma_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T22:28:28.730362+00:00
-- url     : https://prove2.me/theorems/a3ae9989-ef83-498a-a8a0-81a603a07120
-- title:
--   Lemma 6.2 — the closed whole-cube problem and its minimizers
-- statement:
--   Fix $0<\delta<1/2$, put $s=1-2\delta$, and minimize $H_2(a)-H_2(b)$ over the compact closed feasible region
--
--   $$
--   0<a\le\tfrac12,\qquad 0\le b\le a,\qquad \Gamma_H(a,b)\ge s.
--   $$
--
--   The minimum equals $\kappa_H(\delta)$. Every minimizer $(a,b)$ satisfies
--
--   $$
--   0<b<a\le\tfrac12,\qquad \Gamma_H(a,b)=s.
--   $$
--
--   The minimizers are the base points of the one-sided and balanced perturbations of Theorems 6.3 and 6.6.
--
--   **Formalization Note** "The minimum equals $\kappa_H(\delta)$" is stated as: some point of the closed region has value $\kappa_H(\delta)$, and no point of the region has a smaller value.
--
--   Differences from the source:
--
--   - reading: 'the minimum equals κ_H(δ)' → a point of the closed region attains κ_H(δ) and κ_H(δ) is a lower bound on the region; reason: the definition of an attained minimum
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §6.2, Lemma 6.2, p.30 (PDF 32)

import Mathlib
import Definitions.Def_HoneycombCodes_kappaH

set_option autoImplicit false

namespace HoneycombCodes

/-- **Lemma 6.2**, Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2 (sha256 f4b07e31…cd51), p.30 (PDF 32). Fix `0 < δ < 1/2`, put `s = 1 − 2δ`, and minimize
`H₂(a) − H₂(b)` over the compact closed feasible region `0 < a ≤ 1/2`, `0 ≤ b ≤ a`,
`Γ_H(a, b) ≥ s`. The minimum equals `κ_H(δ)`. Every minimizer `(a, b)` satisfies
`0 < b < a ≤ 1/2`, `Γ_H(a, b) = s`.

**Formalization Note.** "The minimum equals κ_H(δ)": some point of the closed region attains the
value `κ_H(δ)` and no point of the region has a smaller value. A minimizer is a point of the closed
region attaining the minimum (`IsWholeCubeMinimizer`). -/
theorem lemma_6_2 (δ : ℝ) (hδ : 0 < δ) (hδ' : δ < 1 / 2) :
    (∃ a b : ℝ, WholeCubeClosed δ a b ∧ H2 a - H2 b = kappaH δ) ∧
    (∀ a b : ℝ, WholeCubeClosed δ a b → kappaH δ ≤ H2 a - H2 b) ∧
    (∀ a b : ℝ, IsWholeCubeMinimizer δ a b →
      0 < b ∧ b < a ∧ a ≤ 1 / 2 ∧ GammaH a b = 1 - 2 * δ) := by sorry

end HoneycombCodes
