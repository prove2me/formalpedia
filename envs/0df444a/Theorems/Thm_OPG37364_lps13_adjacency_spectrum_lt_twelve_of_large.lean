-- Prove2me | Theorems.Thm_OPG37364_lps13_adjacency_spectrum_lt_twelve_of_large
-- name    : OPG37364.lps13_adjacency_spectrum_lt_twelve_of_large
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T09:03:38.878542+00:00
-- url     : https://prove2.me/theorems/66edd183-8287-4bfb-9155-def3aa162e42
-- title:
--   A weak adjacency-spectrum bound for sufficiently large fixed-p=13 LPS graphs
-- statement:
--   There exists a natural threshold $B$ such that for every prime $q>\max\{B,13\}$, every choice of square root of $-1$ in $\mathbb F_q$, and the resulting fixed-$p=13$ LPS graph $G$ on $\mathrm{PGL}_2(\mathbb F_q)$, if $13$ is a quadratic nonresidue modulo $q$, then every real spectral value $\mu$ of the ordinary adjacency matrix satisfies
--   $$
--   \mu\ne14\quad\Longrightarrow\quad\mu<12.
--   $$
--   The threshold is independent of the chosen square root. This is a sufficient weak upper spectral bound, not the Ramanujan bound. Connectedness is not assumed.
-- source:
--   Fixed-p=13 weak consequence in the elementary DSV trace/multiplicity route (Davidoff–Sarnak–Valette, Elementary Number Theory, Group Theory, and Ramanujan Graphs). Uses the classical Frobenius/DSV representation-degree bound through the already proved eigenspace multiplicity theorem 9664d382-ca66-4fcf-a0d7-cd5e86dc95f2, together with the completed arithmetic squared-trace upper bound. No mathematical novelty or full LPS/Ramanujan theorem is claimed.

import Definitions.Def_opg37364_lps13_eigenspaces
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.NumberTheory.LegendreSymbol.Basic
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace OPG37364
theorem lps13_adjacency_spectrum_lt_twelve_of_large :
    ∃ B : ℕ, ∀ {q : ℕ} [Fact q.Prime] (hq : 13 < q), B < q →
      ∀ i : LPS13Root q, legendreSym q 13 = -1 → ∀ μ : ℝ,
        μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ) → μ ≠ 14 → μ < 12 := by sorry
end OPG37364
