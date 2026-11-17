-- Prove2me | Theorems.Thm_KnodelPrimeCordial_case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- name    : KnodelPrimeCordial.case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:31:56.926207+00:00
-- url     : https://prove2.me/theorems/1e123c11-6b2b-427b-9ae5-64fcea12023e
-- title:
--   Assemble offset-two coprime counts by index residue
-- statement:
--   If the six residue-class counts have the stated values, their disjoint union has the target count. Prove by partitioning `Fin (n / 2)` according to `j.val % 6` and simplifying the resulting arithmetic.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling
import Definitions.Def_KnodelPrimeCordial_knodel
import Definitions.Def_KnodelPrimeCordial_labelF

theorem KnodelPrimeCordial.case_mod_6_offset_2_residue_assembly__p2m_7532f8d4_700d_4daa_ba77_23877d6e6e87_a1
    (n : ℕ) (hn : Even n) (h10 : 10 ≤ n) (hmod : n % 12 = 6)
    (h0 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 0 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h1 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 1 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12 + 1)
    (h2 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 2 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 1)
    (h3 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 3 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = 0)
    (h4 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 4 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12)
    (h5 : (Finset.univ.filter fun j : Fin (n / 2) =>
      j.val % 6 = 5 ∧ Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card = n / 12) :
    (Finset.univ.filter fun j : Fin (n / 2) =>
      Nat.Coprime
        (KnodelPrimeCordial.labelF (2 * j.val))
        (KnodelPrimeCordial.labelF
          ((2 * ((j.val + 2 ^ 2 - 1) % (n / 2)) + n - 1) % n))).card =
      (n + 2) / 4 := by sorry
