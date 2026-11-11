-- Prove2me | Theorems.Thm_GaussLocalMaxColoring_Main_theorem_1
-- name    : GaussLocalMaxColoring.Main.theorem_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T15:24:18.628127+00:00
-- url     : https://prove2.me/theorems/493d3937-8689-4103-a80f-e3e6fbb8ddfb
-- title:
--   Theorem 1 ([KTY24], restated) — a sparse independent-set algorithm yields an $n^{\alpha+o(1)}$-coloring (deterministic and randomized clauses)
-- statement:
--   Fix $\alpha\in(0,\tfrac14]$.
--   (a) If a deterministic polynomial-time algorithm finds, in every 3-colorable graph with maximum degree $\Delta<n^{1-2\alpha}$, an independent set of size $n^{1-\alpha-o(1)}$, then a deterministic polynomial-time algorithm colors every 3-colorable graph with $n^{\alpha+o(1)}$ colors.
--   (b) If for every $C>0$ a randomized polynomial-time algorithm finds, in every 3-colorable graph with $\Delta<n^{1-2\alpha}$, an independent set of size $n^{1-\alpha-o(1)}$ with probability at least $1-n^{-C}$, then for every $C>0$ a randomized polynomial-time algorithm properly colors every 3-colorable graph with $n^{\alpha+o(1)}$ colors with probability at least $1-n^{-C}$.
--   Algorithms are programs of the integer RAM `CongruencyTU` (`DetSolves`, `RandSolves` with $n^C$ coins-fraction threshold $1-1/\lceil n^C\rceil$) on the adjacency-matrix input. The theorem is cited from [KTY24] and not proved in the paper.
--
--   Differences from the source:
--   - reading: the printed deterministic statement, applied in the proof of Theorem 6 (p. 5) to the randomized Theorem 5 with "repeating the subroutine sufficiently many times" → the conjunction of (a) the printed deterministic implication (DetSolves ⇒ DetSolves) and (b) the randomized implication used by Theorem 6 (RandSolves for every C ⇒ RandSolves for every C); reason: the paper uses Theorem 1 in the randomized form without stating it (finding I2); clause (a) is the printed statement
--   - encoding: "polynomial time", "with probability at least 1 − n^{−C}" (no machine model named) → CongruencyTU.DetSolves / RandSolves with nvars = ⌈n^C⌉₊ and Feasible = True, adjacency-matrix input, characteristic-vector or label-list output (GoodColoring counts distinct labels); reason: the published machine and graph layer
--   - reading: o(1) in the exponents → one function g → 0 per algorithm (after C in clause (b)), fixed before the input; reason: the paper's uniform asymptotic convention
-- source:
--   Deguchi, Kawarabayashi, Yoneda, Yoneda (2026), An O(n^0.1537)-Coloring Algorithm for 3-Colorable Graphs, arXiv:2610.35859 (SHA-256 9917b0a1…), Theorem 1, printed p. 3 (PDF 5)

import Mathlib
import Definitions.Def_CongruencyTU_Machine
import Definitions.Def_GaussLocalMaxColoring_Main_Machine

open scoped RealInnerProductSpace
open Filter MeasureTheory ProbabilityTheory
open RecGaussColoring.Main
open Classical

namespace GaussLocalMaxColoring.Main

/-- **Theorem 1** ([KTY24], restated; p. 3, PDF 5). Fix `α ∈ (0, 1/4]`.
(a) If a deterministic polynomial-time algorithm finds, in every 3-colorable graph with maximum
degree `Δ < n^{1−2α}`, an independent set of size `n^{1−α−o(1)}`, then a deterministic
polynomial-time algorithm colors every 3-colorable graph with `n^{α+o(1)}` colors.
(b) If for every `C > 0` a randomized polynomial-time algorithm finds such an independent set with
probability at least `1 − n^{−C}`, then for every `C > 0` a randomized polynomial-time algorithm
properly colors every 3-colorable graph with `n^{α+o(1)}` colors with probability at least
`1 − n^{−C}`. -/
theorem theorem_1 (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1 / 4) :
    ((∃ g : ℕ → ℝ, IsLittleO1 g ∧
        CongruencyTU.DetSolves encGraph graphSize (ThreeColDegLt (1 - 2 * α))
          (GoodIndepO (1 - α) g)) →
      ∃ g : ℕ → ℝ, IsLittleO1 g ∧
        CongruencyTU.DetSolves encGraph graphSize ThreeColorable
          (fun I out => GoodColoring I out ((I.n : ℝ) ^ (α + g I.n)))) ∧
    ((∀ C : ℝ, 0 < C → ∃ g : ℕ → ℝ, IsLittleO1 g ∧
        CongruencyTU.RandSolves encGraph graphSize (ThreeColDegLt (1 - 2 * α))
          (fun I => ⌈(I.n : ℝ) ^ C⌉₊) (fun _ => True) (GoodIndepO (1 - α) g)) →
      ∀ C : ℝ, 0 < C → ∃ g : ℕ → ℝ, IsLittleO1 g ∧
        CongruencyTU.RandSolves encGraph graphSize ThreeColorable
          (fun I => ⌈(I.n : ℝ) ^ C⌉₊) (fun _ => True)
          (fun I out => GoodColoring I out ((I.n : ℝ) ^ (α + g I.n)))) := by sorry

end GaussLocalMaxColoring.Main
