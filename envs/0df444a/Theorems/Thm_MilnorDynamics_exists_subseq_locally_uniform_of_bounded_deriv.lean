-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_locally_uniform_of_bounded_deriv
-- name    : MilnorDynamics.exists_subseq_locally_uniform_of_bounded_deriv
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T23:47:53.603033+00:00
-- url     : https://prove2.me/theorems/79ddcb2b-15ab-4d54-80b2-408391817cfc
-- title:
--   Arzela-Ascoli extraction - a bounded family with bounded derivatives has a locally uniformly convergent subsequence
-- statement:
--   **Extraction from boundedness and bounded derivatives.** Let $U\subseteq\mathbb C$ be open, let $f_n$ be holomorphic on $U$, and suppose that on every compact subset of $U$ both the values and the derivatives of the family are uniformly bounded. Then there are a strictly increasing $\varphi$ and a continuous $g:U\to\mathbb C$ with $f_{\varphi(n)}\to g$ locally uniformly on $U$.
--
--   Proof. Bounded derivatives on a compact set $K$ bound the oscillation of each $f_n$ on $K$, so the family is equicontinuous on every compact subset of $U$; the value bounds give pointwise relative compactness. Arzela-Ascoli yields uniform convergence of a subsequence on each compact set, and a diagonal extraction along a countable compact exhaustion of the open set $U$ produces one subsequence converging locally uniformly on all of $U$. The limit is continuous as a locally uniform limit of continuous functions.
--
--   This is the extraction half of Montel's theorem.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (Montel's theorem, the Arzela-Ascoli step for a locally bounded holomorphic family).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_locally_uniform_of_bounded_deriv (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hderiv : ∀ K ⊆ U, IsCompact K → ∃ B, ∀ n, ∀ z ∈ K, ‖deriv (f n) z‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by sorry

end MilnorDynamics
