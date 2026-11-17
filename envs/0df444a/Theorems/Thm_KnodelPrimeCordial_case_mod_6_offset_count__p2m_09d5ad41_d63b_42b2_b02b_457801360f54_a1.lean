-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_count__p2m_09d5ad41_d63b_42b2_b02b_457801360f54_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_count__p2m_09d5ad41_d63b_42b2_b02b_457801360f54_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:10:13.521013+00:00
-- url     : https://prove2.me/theorems/0097d18c-892d-47ab-91e0-b6172f62f5ff
-- title:
--   Coprime index count for each residue-six neighbor offset
-- statement:
--   For each of the three neighbor offsets, count the indices whose endpoint labels are coprime: the middle offset contributes `(n - 2) / 4`, while the first and third each contribute `(n + 2) / 4`. The hypotheses, including evenness, the lower bound, and the residue condition, are preserved. A proof can split ordinary indices into classes modulo 6 and handle the wrapped indices separately; the minimum admissible value is `n = 18`, where the three counts are 5, 4, and 5.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF
open scoped BigOperators

theorem KnodelPrimeCordial.case_mod_6_offset_count__p2m_09d5ad41_d63b_42b2_b02b_457801360f54_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6) (k : Fin 3) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ k.val - 1) % (n / 2)) + n - 1) % n))).card =
      if k.val = 1 then (n - 2) / 4 else (n + 2) / 4 := by sorry
