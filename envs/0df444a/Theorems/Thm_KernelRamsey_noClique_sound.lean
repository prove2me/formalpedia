-- Prove2me | Theorems.Thm_KernelRamsey_noClique_sound
-- name    : KernelRamsey.noClique_sound
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-11-24T16:42:54.55847+00:00
-- url     : https://prove2.me/theorems/8b57b433-3c97-4138-8280-a74210685099
-- title:
--   Soundness of a bit-mask clique search
-- statement:
--   The function `noClique rows fuel k cand` searches the graph encoded by `rows` for a clique of size $k$ whose vertices all lie in the candidate mask `cand`. It splits on the highest candidate $p$: either $p$ is in the clique and the other $k-1$ vertices are neighbours of $p$, or $p$ is not and the clique lies among the remaining candidates. The recursion is structural in the fuel. The theorem says that if the search returns `true` for any fuel, no set of $k$ vertices among the candidates is a clique in the sense that every ordered pair of distinct members is joined by a set bit. It holds for every list of natural numbers; no symmetry of the rows is assumed.
-- source:
--   B. W. Daugherty, G. Ward and S. Ryan, Kernel-Evaluated Ramsey Bounds in Lean 4, version 1.0.0, 2026, doi:10.5281/zenodo.24505785.

import Mathlib
import Definitions.Def_KernelRamsey_Mask
open KernelRamsey

theorem KernelRamsey.noClique_sound {n : Nat} (rows : List Nat) :
    ∀ (f k cand : Nat), noClique rows f k cand = true →
      ∀ S : Finset (Fin n), S.card = k → (∀ v ∈ S, cand.testBit v.val = true) →
        ¬ IsMaskClique rows S := by sorry
