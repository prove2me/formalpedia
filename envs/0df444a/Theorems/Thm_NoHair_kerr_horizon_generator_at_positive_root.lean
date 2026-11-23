-- Prove2me | Theorems.Thm_NoHair_kerr_horizon_generator_at_positive_root
-- name    : NoHair.kerr_horizon_generator_at_positive_root
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T10:05:24.916509+00:00
-- url     : https://prove2.me/theorems/6e328bbb-8d15-49c8-999b-ffc3876a21af
-- title:
--   The vacuum Kerr Killing generator and its signed surface gravity at any positive horizon root
-- statement:
--   Let $R>0$ solve $R^2-2mR+a^2=0$. The complete Killing generator $X=\partial_t+[a/(R^2+a^2)]\partial_\varphi$ is null at $r=R$. In every model atlas chart it satisfies $d(g(X,X))=-2\kappa\,g(X,\cdot)$ there, with $\kappa=(R-m)/(R^2+a^2)$. The formula covers both horizon roots and also their coalescence.
-- source:
--   B. Carter, Black hole equilibrium states, in Black Holes (Les Houches 1972), Gordon and Breach (1973). See also S. Carroll, Lecture Notes on General Relativity, §7, https://ned.ipac.caltech.edu/level5/March01/Carroll3/Carroll7.html. The proof checks the identities directly in the mission’s ingoing Kerr–Schild coordinates.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_horizon_generator_at_positive_root (m a R : ℝ) (hR : 0 < R) (hroot : R^2-2*m*R+a^2 = 0) :
    let A := R^2+a^2
    let Ω := a/A
    let κ := (R-m)/A
    let g := kerrNewmanMetricField m a 0
    let F := kerrNewmanFieldField a 0
    ∃ χ : ℝ → kerrNewmanSpacetime a → kerrNewmanSpacetime a,
      IsSymmetryFlow g F χ ∧
      (∀ x, (flowGenerator χ x : E4) = WithLp.toLp 2 ![1,-Ω*x.val 2,Ω*x.val 1,0]) ∧
      ∀ x : kerrNewmanSpacetime a, ksRadius a x.val = R →
        g x (flowGenerator χ x) (flowGenerator χ x) = 0 ∧
        ∀ e ∈ atlas E4 (kerrNewmanSpacetime a), ∀ y ∈ e.target, e.symm y = x → ∀ i : Fin 4,
          coordPartial (fun z => g (e.symm z) (flowGenerator χ (e.symm z)) (flowGenerator χ (e.symm z))) i y =
            -2*κ*loweredCoeffs g (flowGenerator χ) e.symm y i := by
  sorry
