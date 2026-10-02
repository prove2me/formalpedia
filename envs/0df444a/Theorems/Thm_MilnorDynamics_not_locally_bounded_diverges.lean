-- Prove2me | Theorems.Thm_MilnorDynamics_not_locally_bounded_diverges
-- name    : MilnorDynamics.not_locally_bounded_diverges
-- status  : Disproved
-- author  : @WillR
-- created : 2026-09-30T17:35:53.043348+00:00
-- url     : https://prove2.me/theorems/3c632077-6f90-4a04-80b6-89b663e0f2f9
-- title:
--   Montel escape step — a holomorphic family that is not locally bounded diverges locally uniformly
-- statement:
--   **The escape step of Montel's theorem.** Let $U\subseteq\mathbb C$ be a connected open set and let $f_n:U\to\mathbb C\setminus\{0,1\}$ be holomorphic maps. Suppose the family $(f_n)$ is **not locally bounded**: there is a compact $K\subseteq U$ such that $\sup_{n}\sup_{z\in K}|f_n(z)|=\infty$. Then the sequence **diverges locally uniformly from** $\mathbb C\setminus\{0,1\}$: for every compact $K_0\subseteq U$ and every compact $K'\subseteq\mathbb C\setminus\{0,1\}$ one has $f_n(K_0)\cap K'=\emptyset$ for all sufficiently large $n$.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, ISBN 978-0-691-12488-9, §3, pp. 32-34: the 'otherwise the family is not locally bounded, hence it diverges from every compact subset of the target' step of the proof of Montel's theorem and Corollary 3.3. The supporting preconnected-image clopen argument is the same one formalised in Milnor's Lemma 3.5 (`MilnorDynamics.diverging_subseq_tendsto_puncture`, proved on this platform)

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem not_locally_bounded_diverges (U : Set ℂ) (hU : IsOpen U)
    (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M)) :
    DivergesLocallyUniformlyFrom f U ({0, 1}ᶜ : Set ℂ) := by sorry

end MilnorDynamics
