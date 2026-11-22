-- Prove2me | Theorems.Thm_NoHair_kerrNewman_mass_shell_compact_limit
-- name    : NoHair.kerrNewman_mass_shell_compact_limit
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:52:26.034059+00:00
-- url     : https://prove2.me/theorems/902bc027-c150-42e7-a09b-a7ef36af5cd7
-- title:
--   Compact limits of causal curves in the Kerr–Newman region r > m
-- statement:
--   For an admissible Kerr–Newman parameter triple let $S=\{r>m\}$. If $K$ is a compact subset of $S$, then a limit of endpoint pairs joined by future causal curves in $K$ is joined by a future causal curve in $S$, with coinciding endpoints allowed. This extends the local compact-limit result through the ordinary outer horizon in the subextremal case. In particular it applies to the horizon-penetrating Schwarzschild region needed for the mass-one cutoff counterexample.
-- source:
--   Extension of the verified Kerr–Newman exterior compact-limit and normal-neighborhood proofs on Prove2Me. The larger region is used in the horizon-penetrating Schwarzschild counterexample.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped Manifold ContDiff

theorem NoHair.kerrNewman_mass_shell_compact_limit (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' {z | m < ksRadius a z}
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by sorry
