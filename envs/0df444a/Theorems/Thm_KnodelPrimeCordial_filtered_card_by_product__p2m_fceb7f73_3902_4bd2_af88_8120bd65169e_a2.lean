-- Prove2me | Theorems.Thm_KnodelPrimeCordial_filtered_card_by_product__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- name    : KnodelPrimeCordial.filtered_card_by_product__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T11:22:30.344342+00:00
-- url     : https://prove2.me/theorems/8b32ba14-6b64-4cd3-920a-558849d1e15e
-- title:
--   Filtered cardinality over a product splits by fibers
-- statement:
--   For a bijection from `Fin m × Fin 3` onto a finite set, the number of elements satisfying a predicate equals the sum, over the second coordinate, of the predicate counts in each fiber.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib

theorem KnodelPrimeCordial.filtered_card_by_product__p2m_fceb7f73_3902_4bd2_af88_8120bd65169e_a2
    {α : Type*} [Fintype α] [DecidableEq α]
    (m : ℕ) (e : Fin m × Fin 3 → α) (s : Finset α) (P : α → Prop)
    [DecidablePred P]
    (he : Set.BijOn e Set.univ (↑s : Set α)) :
    (s.filter P).card =
      ∑ k : Fin 3, (Finset.univ.filter fun j : Fin m => P (e (j, k))).card := by sorry
