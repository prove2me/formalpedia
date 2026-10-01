-- Prove2me | Theorems.Thm_MilnorDynamics_locally_bounded_subseq_locally_uniform
-- name    : MilnorDynamics.locally_bounded_subseq_locally_uniform
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T17:28:45.458649+00:00
-- url     : https://prove2.me/theorems/5b631010-6dca-453f-8c87-809e48d9ae3f
-- title:
--   Arzela-Ascoli extraction — a locally bounded sequence of continuous maps has a locally uniform subsequence
-- statement:
--   **Arzelà–Ascoli extraction.** Let $U\subseteq\mathbb C$ be open and let $(f_n)_{n\in\mathbb N}$ be a sequence of continuous maps $f_n:U\to\mathbb C$ that is uniformly bounded on every compact subset of $U$ (a *locally bounded* family). Then there is a strictly increasing $\varphi:\mathbb N\to\mathbb N$ and a continuous $g:U\to\mathbb C$ such that $f_{\varphi(n)}$ converges to $g$ locally uniformly on $U$, i.e. uniformly on every compact $K\subseteq U$.
-- source:
--   Arzela-Ascoli compactness for locally bounded families of continuous maps; the step of Milnor, Dynamics in One Complex Variable, 3rd ed., §3, pp. 32-34, that produces the locally uniform limit before the Hurwitz dichotomy is applied

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem locally_bounded_subseq_locally_uniform (U : Set ℂ) (hU : IsOpen U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, ContinuousOn (f n) U)
    (hb : ∀ K ⊆ U, IsCompact K → ∃ M, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ g : ℂ → ℂ, ContinuousOn g U ∧
      TendstoLocallyUniformlyOn (fun n => f (φ n)) g atTop U := by sorry

end MilnorDynamics
