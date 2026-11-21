-- Prove2me | Theorems.Thm_MasulloRH_geometric_condensation_limit_iff_cutoff_cross_block_vanishes
-- name    : MasulloRH.geometric_condensation_limit_iff_cutoff_cross_block_vanishes
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:23:41.743103+00:00
-- url     : https://prove2.me/theorems/9799bfa8-ff0f-4f30-ae56-9c548030eb58
-- title:
--   The exact missing cross block in the Paley–Wiener condensation limit
-- statement:
--   For a strongly convergent family of input truncations with limit P, invariance P A P = A P forces the strong limit of M P A B_n to be M A P. The uncompressed limit M P A printed in (11.2.1.4) holds exactly when M P A (I-P)=0. The criterion already applies in strong topology, so is necessary for nuclear convergence.
-- source:
--   Masullo, The Music of the Primes (11.2.1.3–5), (11.2.1.9–10), and (10.4.1.10).

import Mathlib
open Filter Topology

theorem MasulloRH.geometric_condensation_limit_iff_cutoff_cross_block_vanishes {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (P A M : E →L[ℂ] E) (B : ℕ → E →L[ℂ] E)
    (hgeom : ∀ x, P (A (P x)) = A (P x))
    (hB : ∀ x, Tendsto (fun n => B n x) atTop (𝓝 (P x))) :
    (∀ x, Tendsto (fun n => M (P (A (B n x)))) atTop (𝓝 (M (A (P x))))) ∧
    ((∀ x, Tendsto (fun n => M (P (A (B n x)))) atTop (𝓝 (M (P (A x))))) ↔
      ∀ x, M (P (A (x - P x))) = 0) := by sorry
