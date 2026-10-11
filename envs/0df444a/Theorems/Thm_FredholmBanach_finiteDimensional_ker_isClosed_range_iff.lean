-- Prove2me | Theorems.Thm_FredholmBanach_finiteDimensional_ker_isClosed_range_iff
-- name    : FredholmBanach.finiteDimensional_ker_isClosed_range_iff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-10T22:44:53.573883+00:00
-- url     : https://prove2.me/theorems/642c0649-8d5d-4bed-955d-1757e42e17ca
-- title:
--   Finite-dimensional kernel and closed range: characterization by bounded sequences
-- statement:
--   Let $\mathbb{K}$ be $\mathbb{R}$ or $\mathbb{C}$, let $E$, $F$ be Banach spaces over $\mathbb{K}$, and let $u:E\to F$ be a bounded linear map. Then the following are equivalent:
--
--   1. $\operatorname{Ker}u$ is finite-dimensional and $\operatorname{Im}u$ is closed in $F$;
--   2. every bounded sequence $(x_n)$ in $E$ for which $(u(x_n))$ converges in $F$ has a convergent subsequence in $E$.
--
--   Condition 2 characterizes the operators with finite-dimensional kernel and closed range by a property of sequences. It is reusable for stability statements about this class of operators, such as perturbation results.
--
--   **Formalization Note.** $\mathbb{K}$ is an `RCLike` field and $E$, $F$ are complete normed spaces over it. A bounded sequence is `x : ℕ → E` with `∃ C, ∀ n, ‖x n‖ ≤ C`; convergence of $(u(x_n))$ to some `y : F` is `Filter.Tendsto (fun n => u (x n)) Filter.atTop (𝓝 y)`; a convergent subsequence is a strictly monotone `φ : ℕ → ℕ` and a point `a : E` with `Filter.Tendsto (x ∘ φ) Filter.atTop (𝓝 a)`. Kernel and range are `u.ker` and `u.range`.
-- source:
--   Auxiliary statement for N. Bourbaki, Théories spectrales, Chapitres III à V, Springer (2023), https://doi.org/10.1007/978-3-031-19505-1, Chapitre III, § 5, n° 2, Théorème 1, p. TS III.72

import Definitions.Def_FredholmBanach_Setting

namespace FredholmBanach

open Topology

/-- For a bounded linear map `u` between Banach spaces, `u` has finite-dimensional kernel and
closed range if and only if every bounded sequence `x` such that `u ∘ x` converges has a
convergent subsequence. -/
theorem finiteDimensional_ker_isClosed_range_iff {𝕜 E F : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F] (u : E →L[𝕜] F) :
    (FiniteDimensional 𝕜 u.ker ∧ IsClosed (u.range : Set F)) ↔
      ∀ x : ℕ → E, (∃ C, ∀ n, ‖x n‖ ≤ C) →
        ∀ y : F, Filter.Tendsto (fun n => u (x n)) Filter.atTop (𝓝 y) →
          ∃ a : E, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (x ∘ φ) Filter.atTop (𝓝 a) := by sorry

end FredholmBanach
