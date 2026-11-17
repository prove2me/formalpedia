-- Prove2me | Theorems.Thm_HZTractability_Supplement_theorem_1_3
-- name    : HZTractability.Supplement.theorem_1_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T09:31:15.662962+00:00
-- url     : https://prove2.me/theorems/f3b5544d-ec93-49cb-a53a-0adbd2bec477
-- title:
--   Theorem 1.3 — two marginal slopes: an exact equilibrium with minimum-expenditure tie-breaking in strongly polynomial time
-- statement:
--   Consider HZ markets with $N\ge1$ buyers and goods and two-slope utilities (1): $U_i(x_i)=\sum_j f_{ij}(x_{ij})$ with $f_{ij}(t)=c^{(2)}_it+(c^{(1)}_i-c^{(2)}_i)\min\{t,\tau_{ij}\}$, rational $c^{(1)}_i\ge c^{(2)}_i\ge0$ and rational $\tau_{ij}\in[0,1]$.
--
--   There is a single algorithm on the unit-cost rational arithmetic RAM (addition, subtraction, multiplication, division and comparison at unit cost, integer program constants) and constants $C,d$ such that, on every such instance with binary input length $L$, it halts within
--   $$C\,(N+1)^d$$
--   steps, every number it holds at any time is a rational of encoding length at most $C\,(L+1)^d$, and its output $(x,p)$ is an exact normalized HZ equilibrium in which each buyer receives a minimum-expenditure bundle among her utility-maximizing affordable unit bundles.
--
--   The step bound depends on $N$ only, not on the magnitudes of the numbers: the algorithm is strongly polynomial. It marks the tractable side of the frontier opposite to the three-slope hardness of Corollary 1.4.
--
--   **Formalization Note** The machine is the published `SmaleNinth.RAMProgram` with `SepQPTardos.Main.Admissible`, `listMem` and `ComputesWithin`; the input is the list $N, c^{(1)}, c^{(2)}, \tau$ row-major, and the output cells hold $x$ row-major followed by $p$. The program is fixed before the instance. Existence of the equilibrium is part of the conclusion.
--
--   Differences from the source:
--   - encoding: can be computed in strongly polynomial time → ∃ one admissible program R of the unit-cost rational RAM (SmaleNinth.RAMProgram, SepQPTardos.Main.Admissible) and C, d with ComputesWithin R (listMem input) (C·(N+1)^d) (C·(L+1)^d) Out for every valid instance; reason: the standard definition: a number of arithmetic operations polynomial in the number of input numbers (N² + 2N + 1) and intermediate numbers of encoding length polynomial in the input length; these are exactly the two bounds of the paper's proof (O(N⁶) operations, Lemma 6.9)
--   - encoding: rational input in (1); the computed equilibrium → memory cells holding N, c^{(1)}, c^{(2)}, τ row-major; output x row-major in cells 0, …, N²−1 and p in cells N², …, N²+N−1; reason: a fixed input and output layout of the machine
--   - encoding: exact normalized HZ equilibrium; each buyer receives a minimum-expenditure bundle among her utility-maximizing affordable bundles → IsMinExpEq util x p: feasibility, normalized p ≥ 0, p·x_i ≤ 1, U_i(x_i) ≥ U_i(y) and (U_i(y) ≥ U_i(x_i) → p·x_i ≤ p·y) for every budget-one unit bundle y; reason: §2.2 and Definition 6.1 verbatim with the maximum of (OptBundle) written as attained; affordable bundles are unit bundles with p·y ≤ 1
-- source:
--   Panageas, Shein, Taherijam, Vazirani, Exploring the Tractability Frontier of Hylland–Zeckhauser Models, arXiv:2610.35848 (held version, sha256 74b7bf9f…), Theorem 1.3, p.2 (PDF p.4); proof pp.24–33 (PDF pp.26–35), Lemma 6.9 p.32

import Mathlib
import Definitions.Def_SmaleNinth_RealRAM
import Definitions.Def_SepQPTardos_Main_Encoding
import Definitions.Def_SepQPTardos_Main_Machine
import Definitions.Def_HZTractability_Supplement_TwoSlopeInst

namespace HZTractability.Supplement

/-- **Theorem 1.3 (Two marginal slopes)** (Panageas–Shein–Taherijam–Vazirani, arXiv:2610.35848, held
version, sha256 74b7bf9f…, p.2 (PDF 4); proof pp.24–33 (PDF 26–35)): "For rational input in (1), an
exact normalized HZ equilibrium can be computed in strongly polynomial time. Each buyer receives a
minimum-expenditure bundle among her utility-maximizing affordable bundles."

There is one admissible program `R` of the unit-cost rational arithmetic RAM and constants `C, d` such
that for every valid two-slope instance (`N ≥ 1`, `c^{(1)}_i ≥ c^{(2)}_i ≥ 0`, `τ_ij ∈ [0, 1]`), the run
of `R` on the input list `[N, c^{(1)}, c^{(2)}, τ row-major]` accepts within `C·(N + 1)^d` steps, every
number held in a register or memory cell during the run is a rational of encoding length at most
`C·(L + 1)^d` (`L` the binary input length), and the output memory holds an exact normalized HZ
equilibrium with minimum-expenditure tie-breaking for the input's utilities (1).

**Formalization Note** The machine is the published `SmaleNinth.RAMProgram` with the published
`SepQPTardos.Main.Admissible` (integer program constants only), `listMem`, `ComputesWithin` and
`ratLen`: `+, −, ×, ÷` and comparisons at unit cost. "Strongly polynomial" is the step bound depending
on `N` only (the instance has `N² + 2N + 1` numbers) together with the polynomial bound on every
intermediate encoding length (Lemma 6.9). The program is fixed before the instance (uniform in `N`).
Existence of the equilibrium is part of the conclusion. -/
theorem theorem_1_3 :
    ∃ R : SmaleNinth.RAMProgram, SepQPTardos.Main.Admissible R ∧ ∃ C d : ℕ,
      ∀ I : TwoSlopeInst, I.Valid →
        SepQPTardos.Main.ComputesWithin R (SepQPTardos.Main.listMem I.input)
          (C * (I.N + 1) ^ d) (C * (I.inputLen + 1) ^ d) I.Out := by sorry

end HZTractability.Supplement
