-- Prove2me | Theorems.Thm_KnodelPrimeCordial_knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- name    : KnodelPrimeCordial.knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:37:23.642669+00:00
-- url     : https://prove2.me/theorems/71d2ce87-07af-4514-ba77-3374083c1b30
-- title:
--   Distinctness of the three degree-three Knödel offsets
-- statement:
--   For modulus n/2 at least 5, the indices j, j+1, and j+3 modulo n/2 are pairwise distinct. The three offset differences are 1, 3, and 2, each positive and smaller than the modulus, including when reduction wraps around.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_knodel

theorem KnodelPrimeCordial.knodel_three_offsets_distinct__p2m_1abdd4c6_f2e4_4e48_a474_4d81735dcf17_a1 (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (j : Fin (n / 2)) : let x : Fin (n / 2) := j; let y : Fin (n / 2) := ⟨(j.val + 1) % (n / 2), Nat.mod_lt _ (by omega)⟩; let z : Fin (n / 2) := ⟨(j.val + 3) % (n / 2), Nat.mod_lt _ (by omega)⟩; x ≠ y ∧ x ≠ z ∧ y ≠ z := by sorry
