-- Prove2me | Theorems.Thm_MasulloRepair_halfline_compact_window_cofinal_convergence
-- name    : MasulloRepair.halfline_compact_window_cofinal_convergence
-- status  : Proved
-- author  : @ibecca
-- created : 2026-11-21T01:53:37.478933+00:00
-- url     : https://prove2.me/theorems/2cf713aa-17bf-4fe0-9b9f-b73f1670aac5
-- title:
--   Cofinal compact windows give an intrinsic half-line convergence criterion
-- statement:
--   Let $a\in\mathbf R$ and let $(c_n)_{n\ge0}$ be any sequence in $[a,\infty)$ unbounded above: for each $b\in\mathbf R$ some $c_n\ge b$. Let $\mathcal F$ be a filter on an index set $X$, and let $g_x:\mathbf R\to\mathbf R$ be measurable and nonnegative on $(0,\infty)$. Suppose that for each $x$ and $n$,
--   $$t\longmapsto g_x(t)\max\{t^{2a},t^{2c_n}\}$$
--   is integrable on the positive ray. Write
--   $$Q_x(u,v)=\left(\int_0^\infty g_x(t)\max\{t^{2u},t^{2v}\}\,dt\right)^{1/2}.$$
--   Then every compact-subwindow integrand with $a\le u\le v$ is integrable, and
--   $$\bigl[\forall n,\ Q_x(a,c_n)\longrightarrow_{\mathcal F}0\bigr]
--   \quad\Longleftrightarrow\quad
--   \bigl[\forall a\le u\le v,\ Q_x(u,v)\longrightarrow_{\mathcal F}0\bigr].$$
--
--   Thus the compact-window convergence criterion is independent of the chosen cofinal sequence; neither monotonicity of that sequence nor a uniform bound over it is required. Applied to the error densities $g_x(t)=|\varphi_x(t)-\varphi(t)|^2(1+|\log t|^2)^{s/2}/t$, this is the convergence criterion for the proposed family of compact-window norms. It repairs the choice-of-sequence assertion after replacing the infinite uniform supremum by a family of norms.
--
--   **Formalization Note.** The conclusion quantifies over arbitrary filters, hence includes arbitrary nets rather than only sequences. It proves the integral domination and convergence assertions, not completeness, normability, a Mellin-transform isomorphism, or a trace formula.
-- source:
--   Corrected replacement statements for A. M. Masullo, The Music of the Primes, Definition 9.2.2.1, equation (9.2.2.3), and Lemma 9.2.2.2(3)(a), equations (9.2.2.6)-(9.2.2.7), printed pp. 412-413; frozen draft https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf . The finiteness obstruction and compact-subinterval topology alternative were reported by Yi in Prove2Me mission comment a96ab6a0-9f70-4b3f-ab3e-8c7e38a823f2, mission 638f9b7f-e232-4624-ba08-5889465bb1e7. These are new repair lemmas, not assertions that the original unrestricted uniform-norm statement is valid. General measurable-density and arbitrary-filter form of the compact-subinterval replacement proposed in Yi's report. It uses the source's pointwise comparisons (9.2.2.14)-(9.2.2.16), whose compact-window endpoint consequence was formalized as a224bfd6-48df-4521-8f7a-d5589f0c3413.

import Mathlib

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal

theorem MasulloRepair.halfline_compact_window_cofinal_convergence {α : Type*} (l : Filter α) (g : α → ℝ → ℝ)
    (hg : ∀ x : α, Measurable (g x))
    (hgn : ∀ (x : α) (t : ℝ), 0 < t → 0 ≤ g x t)
    (a : ℝ) (c : ℕ → ℝ) (hca : ∀ n : ℕ, a ≤ c n)
    (hc : ∀ b : ℝ, ∃ n : ℕ, b ≤ c n)
    (hi : ∀ (x : α) (n : ℕ),
      IntegrableOn (fun t : ℝ => g x t * max (t^(2*a)) (t^(2*c n))) (Ioi 0)) :
    (∀ (x : α) (u v : ℝ), a ≤ u → u ≤ v →
      IntegrableOn (fun t : ℝ => g x t * max (t^(2*u)) (t^(2*v))) (Ioi 0)) ∧
    ((∀ n : ℕ, Tendsto
        (fun x : α => Real.sqrt (∫ t in Ioi (0 : ℝ), g x t * max (t^(2*a)) (t^(2*c n))))
        l (𝓝 0)) ↔
      ∀ u v : ℝ, a ≤ u → u ≤ v → Tendsto
        (fun x : α => Real.sqrt (∫ t in Ioi (0 : ℝ), g x t * max (t^(2*u)) (t^(2*v))))
        l (𝓝 0)) := by sorry
