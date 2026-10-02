-- Prove2me | Theorems.Thm_MilnorDynamics_exists_subseq_escapes_on_compacts
-- name    : MilnorDynamics.exists_subseq_escapes_on_compacts
-- status  : Open
-- author  : @WillR
-- created : 2026-10-01T15:43:41.007545+00:00
-- url     : https://prove2.me/theorems/484390ac-3b9e-4853-afdd-915300b51758
-- title:
--   Per-compact escape of an unbounded holomorphic family omitting two values
-- statement:
--   **Per-compact escape.** Let $U \subseteq \mathbb C$ be connected and open, and let $f_n : U \to \mathbb C \setminus \{0,1\}$ be holomorphic. If the family is not locally bounded --- some compact $K \subseteq U$ has no common bound for the $|f_n|$ --- then for *each* fixed compact $K_0 \subseteq U$ there is a strictly increasing $\varphi$ with $|f_{\varphi(n)}(z)| > R$ for all $z \in K_0$ and all sufficiently large $n$, for every real $R$.
--
--   This is the per-compact form of the escape step in Milnor's proof of Montel's theorem (Milnor, *Dynamics in One Complex Variable*, 3rd ed., Section 3). It is the analytic content of `MilnorDynamics.exists_subseq_escapes_locally`, whose extra content is the diagonal extraction that upgrades "one subsequence for each prescribed compact" to "one subsequence that works on every compact simultaneously". Proving the parent from this child is therefore a combinatorial packaging argument (nested extractions of an escaping sequence, since a subsequence of an eventually escaping sequence still escapes).
--
--   The content is Zalcwasser's theorem / the compactness of families omitting two values: the underlying analytic input is Schottky's theorem, isolated on the platform as `MilnorDynamics.schottky_bound`.
-- source:
--   J. Milnor, Dynamics in One Complex Variable, 3rd ed., Annals of Mathematics Studies 160, Princeton University Press, 2006, Section 3 (escape step in the proof of Montel's theorem), stated per compact as in the classical Zalcwasser/Schottky treatment of families omitting two values.

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

theorem exists_subseq_escapes_on_compacts (U : Set ℂ) (hU : IsOpen U) (hUc : IsConnected U)
    (f : ℕ → ℂ → ℂ)
    (hf : ∀ n, DifferentiableOn ℂ (f n) U ∧ MapsTo (f n) U ({0, 1}ᶜ : Set ℂ))
    (hbdd : ∃ K ⊆ U, IsCompact K ∧
      ¬ (∃ M : ℝ, ∀ n, ∀ z ∈ K, ‖f n z‖ ≤ M))
    (K₀ : Set ℂ) (hK₀U : K₀ ⊆ U) (hK₀ : IsCompact K₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ R : ℝ, ∀ᶠ n in atTop, ∀ z ∈ K₀, R < ‖f (φ n) z‖ := by sorry

end MilnorDynamics
