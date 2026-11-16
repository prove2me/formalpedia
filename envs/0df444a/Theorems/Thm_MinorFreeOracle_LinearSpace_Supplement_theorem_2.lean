-- Prove2me | Theorems.Thm_MinorFreeOracle_LinearSpace_Supplement_theorem_2
-- name    : MinorFreeOracle.LinearSpace.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T12:15:00.149028+00:00
-- url     : https://prove2.me/theorems/ab7d07c2-b7e8-4bbd-990d-cbc4f30e1f20
-- title:
--   Theorem 2 — space–query trade-off for exact distance oracles in H-minor-free graphs
-- statement:
--   There are natural numbers $c$ and $p$ such that the following holds for every finite simple graph $H$. There exist a preprocessing program $\mathrm{Pre}$, a query program $\mathrm{Qry}$ and a constant $C>0$, depending only on $H$, which work for every connected simple $n$-vertex $H$-minor-free graph $G$ with nonnegative real edge weights and every integer trade-off parameter $\sigma\ge 1$ with
--
--   $$
--   n\log\log n\;\le\;\sigma\;\le\;n^2 .
--   $$
--
--   Given $G$ and $\sigma$, preprocessing takes at most $Cn^c$ steps and stores at most $C\sigma$ cells, counting the input; from the stored memory, every query pair $s,t$ is answered with the exact distance $d_G(s,t)$ within
--
--   $$
--   C\,\frac{n}{\sqrt{\sigma}}\,\log^{p}(n+2)
--   $$
--
--   steps. In the paper's notation: an exact distance oracle with $O(\sigma)$ space and $\tilde O(n/\sqrt{\sigma})$ query time, constructed in $O(n^c)$ time, where $c$ does not depend on $H$.
--
--   This is the paper's companion trade-off to Theorem 1 (the goal). At $\sigma = n^2$ it gives polylogarithmic query time with quadratic space, and at $\sigma = n\log\log n$ it gives query time $\tilde O(\sqrt{n/\log\log n})$ with almost linear space; it improves the $O(n^2/\sigma)$ query time of the separator-based trade-off of Djidjev (1997) to $\tilde O(n/\sqrt\sigma)$.
--
--   **Formalization Note** The parameter $\sigma$ is an input of one fixed pair of programs, not something the programs or $C$ may depend on. Both exponents $c$ and $p$ are fixed before $H$. The machine, input layout and space accounting are those of the published goal (Theorem 1).
--
--   Differences from the source:
--   - encoding: a finite undirected simple graph G with nonnegative edge weights → a weighted edge list on Fin n with IsSimple, Connected, nonnegative weights and the published branch-set MinorFree; reason: same hypotheses as the published goal; finite enumerations preserve every source instance; Connected is the paper's standing assumption (§3, PDF p.15)
--   - reading: time and space on an unnamed machine model → deterministic finite programs on the published comparison–addition word RAM, word size from n+m+σ+2; reason: the computational model of the published goal; σ ≤ n² keeps words at O(log n) bits
--   - encoding: an exact distance oracle using O(σ) space → halted preprocessing memory from which every query starts with reset registers; space counts distinct preprocessing writes plus the 3+3m input cells; reason: the space convention of the published goal; m = O(n) ≤ O(σ) for a fixed excluded minor
--   - reading: "for a parameter σ", with O-constants depending on H only → one pair of programs and one C per H, with σ given as input and the bounds uniform over every σ in the range; reason: the stronger of the two readings (programs chosen per σ would be the weaker one)
--   - encoding: real σ ∈ [n log log n, n²] → natural σ ≥ 1 with n·log(log n) ≤ σ ≤ n² (Real.log); reason: ⌈σ⌉ stays in the interval because n² is an integer and changes σ and n/√σ by at most a factor 2 when σ ≥ 1; σ ≥ 1 excludes only σ = 0 (possible for n ≤ 2, where log log n is undefined or negative and n/√σ is undefined) and sub-unit σ, which occur only for n ≤ 3 and are absorbed by the constant; the paper does not fix the base of log, and the natural log gives a lower endpoint n·ln ln n ≤ n·log₂log₂ n (n ≥ 2), so the Lean range contains the base-2 range and its endpoints differ by a constant factor absorbed by C
--   - reading: Õ(n/√σ), "factors polynomial in log n" → C·(n/√σ)·log(n+2)^p with p fixed before H; reason: the stronger reading of Õ (exponent not depending on H); log(n+2) instead of log n keeps the factor positive at n = 1, 2 and is within a factor 2^p of log n for n ≥ 2
--   - encoding: O(n^c), O(σ), with c independent of H → one natural c before H and one positive real C after H bounding all three resources for every n ≥ 1; reason: an integer exponent and a common constant absorb the source bounds and the finitely many small inputs without changing their asymptotic strength
-- source:
--   Eunjin Oh, Linear-Space Exact Distance Oracle for Minor-Free Graphs, STOC 2027 submission #160 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/160.pdf, Theorem 2, PDF p.4 (printed p.2); O/Õ convention on the same page; preprocessing discussion PDF p.5 (printed p.3); standing assumptions §3, PDF p.15 (printed p.13)

import Mathlib
import Definitions.Def_MinorFreeOracle_LinearSpace_Graph
import Definitions.Def_MinorFreeOracle_LinearSpace_Supplement_ExactOracleParam

namespace MinorFreeOracle.LinearSpace.Supplement

open MinorFreeOracle.LinearSpace

/-- Oh, Theorem 2, PDF p.4 (printed p.2), with the standing connectedness assumption of §3,
PDF p.15, and the O/Õ convention of PDF p.4 (constants depend on `H` only; Õ suppresses a factor
polynomial in `log n`). The preprocessing exponent `c` and the polylog exponent `p` come before `H`.
For each `H` there is one pair of programs and one positive constant `C`, uniform over all graphs,
all nonnegative weights and every trade-off parameter `σ = k` with `n log log n ≤ σ ≤ n²`; `σ` is an
input of the programs. Preprocessing takes at most `C n^c` steps, storage (input included) is at most
`C σ` cells, and every query is answered exactly within `C (n/√σ) log^p (n + 2)` steps. -/
theorem theorem_2 :
    ∃ c p : ℕ, ∀ (h : ℕ) (H : SimpleGraph (Fin h)),
      ∃ (Pre Qry : RealAPSP.Program) (C : ℝ), 0 < C ∧
        ∀ G : TZLevelsADO.Graph,
          IsSimple G → G.Connected → (∀ e, 0 ≤ G.wt e) → MinorFree G H →
          ∀ k : ℕ, 1 ≤ k →
            (G.n : ℝ) * Real.log (Real.log (G.n : ℝ)) ≤ (k : ℝ) →
            (k : ℝ) ≤ (G.n : ℝ) ^ 2 →
            IsExactOracleParam Pre Qry G k
              (C * (G.n : ℝ) ^ c) (C * (k : ℝ))
              (C * ((G.n : ℝ) / Real.sqrt (k : ℝ)) * Real.log ((G.n : ℝ) + 2) ^ p) := by sorry

end MinorFreeOracle.LinearSpace.Supplement
