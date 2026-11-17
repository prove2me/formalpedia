-- Prove2me | Theorems.Thm_KnodelPrimeCordial_primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1
-- name    : KnodelPrimeCordial.primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:14:56.514975+00:00
-- url     : https://prove2.me/theorems/997a75d7-cde0-465d-99c4-3e69bfa4c2a4
-- title:
--   Transport prime cordial labelings across graph equivalences
-- statement:
--   If two finite simple graphs are related by a vertex equivalence preserving adjacency, any prime cordial labeling of the first graph induces a prime cordial labeling of the second.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

theorem KnodelPrimeCordial.primeCordial_transport__p2m_b71a112c_d89d_4dc4_9a88_bb82c5bac86c_a1
    {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj]
    (e : V ≃ W)
    (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b))
    (f : V → ℕ)
    (hf : KnodelPrimeCordial.IsPrimeCordialLabeling G f) :
    ∃ g : W → ℕ, KnodelPrimeCordial.IsPrimeCordialLabeling H g := by sorry
