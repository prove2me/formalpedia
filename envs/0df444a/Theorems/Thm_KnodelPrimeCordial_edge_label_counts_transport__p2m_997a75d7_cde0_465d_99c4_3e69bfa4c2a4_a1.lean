-- Prove2me | Theorems.Thm_KnodelPrimeCordial_edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1
-- name    : KnodelPrimeCordial.edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-16T10:29:00.193207+00:00
-- url     : https://prove2.me/theorems/ff437e48-e101-4ad2-b4db-c7123e4b813c
-- title:
--   Prime cordial edge-label counts are invariant under graph equivalence
-- statement:
--   An adjacency-preserving equivalence transports each edge to an edge with the same endpoint-label gcd, so both prime-cordial edge-label counts are preserved for any natural-number labeling.
-- source:
--   Haque, Khanam, Shahriar, Prime cordial labeling of Knödel graph, manuscript (2026) (held version, sha256 366502170d8d7c65ccc2fcc6f5373dac872d6efdc838ba9e671eb578e4c08c60), Lemma 2.3, p.3 (PDF p.3); proof pp.4–6

import Mathlib
import Definitions.Def_KnodelPrimeCordial_IsPrimeCordialLabeling

theorem KnodelPrimeCordial.edge_label_counts_transport__p2m_997a75d7_cde0_465d_99c4_3e69bfa4c2a4_a1 {V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W] (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] (e : V ≃ W) (hadj : ∀ a b, G.Adj a b ↔ H.Adj (e a) (e b)) (f : V → ℕ) : (KnodelPrimeCordial.edgesLabelZero G f).card = (KnodelPrimeCordial.edgesLabelZero H (f ∘ e.symm)).card ∧ (KnodelPrimeCordial.edgesLabelOne G f).card = (KnodelPrimeCordial.edgesLabelOne H (f ∘ e.symm)).card := by sorry
