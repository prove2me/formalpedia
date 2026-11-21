-- Prove2me | Theorems.Thm_GRH_smoothed_mobius_character_le_scale
-- name    : GRH.smoothed_mobius_character_le_scale
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-20T23:57:48.152435+00:00
-- url     : https://prove2.me/theorems/5172a9f6-53a4-4471-9878-f93d6e2c50c3
-- title:
--   Uniform linear bound for exponentially smoothed Dirichlet twists of the Möbius function
-- statement:
--   For every Dirichlet character $\chi$ modulo any positive integer $q$ and every positive real scale $D$,
--   $$
--   \left|\sum_{n\ge1}\mu(n)\chi(n)e^{-n/D}\right|\le D.
--   $$
--   The estimate holds with constant one uniformly in the character and the scale. It gives the absolute-value baseline for attempts to prove cancellation of size $O_{q,\chi,\varepsilon}(D^{1/2+\varepsilon})$.
-- source:
--   Direct geometric-series estimate for the exponential sum defined in OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean, definition mobiusExpSum. https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean .

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

theorem GRH.smoothed_mobius_character_le_scale (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (D : ℝ) (hD : 0 < D) :
    ‖OAI.ShortDraftMellin.mobiusExpSum χ D⁻¹‖ ≤ D := by sorry
