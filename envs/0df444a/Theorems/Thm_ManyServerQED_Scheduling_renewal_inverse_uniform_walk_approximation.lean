-- Prove2me | Theorems.Thm_ManyServerQED_Scheduling_renewal_inverse_uniform_walk_approximation
-- name    : ManyServerQED.Scheduling.renewal_inverse_uniform_walk_approximation
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T01:52:13.625603+00:00
-- url     : https://prove2.me/theorems/4dac099a-210e-5ae1-939e-934469626173
-- title:
--   Finite-window approximation of centered renewal counts by the centered epoch walk
-- statement:
--   Suppose a strictly increasing renewal epoch sequence has a centered interpolation with uniformly bounded amplitude and small modulus on a window larger than the observation window. If the counting and space-scale meshes are sufficiently small, the centered and scaled renewal count uniformly approximates the negative of that interpolation evaluated at the deterministic fluid time.
-- source:
--   Supporting lemma for Atar, Mandelbaum, and Reiman, Scheduling a multi class queue with many exponential servers, https://arxiv.org/abs/math/0407058

import Definitions.Def_ManyServerQED_Scheduling_Model
open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

theorem ManyServerQED.Scheduling.renewal_inverse_uniform_walk_approximation (n : ℕ) (hn : 1 ≤ n) (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (u : ℝ → ℝ) (hgrid : ∀ j : ℕ, u ((j:ℝ)/n) = (e j-j)/Real.sqrt n)
    (a T H D δ ε : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hH : a*T+3 ≤ H)
    (hD : ∀ s ∈ Set.Icc (0:ℝ) H, |u s| ≤ D)
    (hDsmall : D/Real.sqrt n < min 1 (δ/4))
    (hNsmall : 1/(n:ℝ) < δ/4) (hRsmall : 1/Real.sqrt n < ε/4) (hε : 0 < ε)
    (hMod : ∀ s ∈ Set.Icc (0:ℝ) H, ∀ t ∈ Set.Icc (0:ℝ) H,
      |s-t| < δ → |u s-u t| < ε/2) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      |(((renewalCount e ((n:ℝ)*a*t)).toNat:ℝ) - (n:ℝ)*a*t)/Real.sqrt n + u (a*t)| < ε := by sorry
