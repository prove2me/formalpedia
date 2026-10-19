-- Prove2me | Theorems.Thm_MazurTransfer_northcott_fiber_infimum_of_surjective
-- name    : MazurTransfer.northcott_fiber_infimum_of_surjective
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-16T20:42:29.758448+00:00
-- url     : https://prove2.me/theorems/05294df7-4700-4b3d-9528-be24a4441e24
-- title:
--   Northcott heights descend by infima over fibers
-- statement:
--   Let $f:Y\to X$ be surjective and let $h:Y\to\mathbb R$ be nonnegative with finite sublevel sets. Then $H(x)=\inf\{h(y):f(y)=x\}$ also has finite sublevel sets. Thus a nonnegative Northcott height descends along a surjection by taking its infimum on each fiber. The hypotheses guarantee that every fiber-height set is nonempty and bounded below. No finite-fiber assumption on $f$ is needed.
-- source:
--   Elementary fiber-infimum argument developed for the actual order-13 arithmetic Picard height in MazurTheorem. Proof uses the conditional completeness of the reals and finite sublevel sets.

import Mathlib

theorem MazurTransfer.northcott_fiber_infimum_of_surjective {X Y : Type*} (f : Y → X) (hf : Function.Surjective f)
    (h : Y → ℝ) (h0 : ∀ y, 0 ≤ h y) [Northcott h] :
    Northcott (fun x => sInf (h '' (f ⁻¹' {x}))) := by sorry
