-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_locally_uniform_of_oscillation_bounded
-- name    : MilnorDynamics.exists_subseq_locally_uniform_of_oscillation_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-01T00:17:53.042166+00:00
-- url     : https://prove2.me/theorems/505c170f-816b-4c83-ae6c-5e6854cdb5bf
-- title:
--   Arzela-Ascoli with a diagonal - bounded and equicontinuous families have a locally uniformly convergent subsequence
-- statement:
--   **Extraction from boundedness and uniform equicontinuity on compacta.** Let $U\subseteq\mathbb C$ be open and let $f_n:U\to\mathbb C$ be a family which is uniformly bounded on every compact subset of $U$ and uniformly equicontinuous on every compact subset of $U$. Then some subsequence converges locally uniformly on $U$ to a continuous limit.
--
--   Proof. On a fixed compact $K\subseteq U$ the family is bounded and equicontinuous, so Arzela-Ascoli makes it relatively sequentially compact for uniform convergence on $K$: some subsequence converges uniformly on $K$. Applying this along a countable compact exhaustion $K_1\subseteq K_2\subseteq\cdots$ of the open set $U$ and passing to a diagonal subsequence yields one strictly increasing index map $\varphi$ such that $f_{\varphi(n)}$ converges uniformly on every $K_j$. Since every compact subset of $U$ is contained in some $K_j$, the convergence is locally uniform on $U$. The limit is continuous because the equicontinuity modulus passes to the limit.
--
--   This is the Arzela-Ascoli half of Montel's theorem for a locally bounded holomorphic family.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (Montel's theorem, the Arzela-Ascoli step).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_locally_uniform_of_oscillation_bounded (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)
    (hmod : ∀ K ⊆ U, IsCompact K → ∀ ε > 0, ∃ δ > 0, ∀ n, ∀ x ∈ K, ∀ y ∈ K,
      ‖x - y‖ < δ → ‖f n x - f n y‖ < ε) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by sorry

end MilnorDynamics
