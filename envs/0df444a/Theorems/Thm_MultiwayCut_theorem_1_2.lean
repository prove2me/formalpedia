-- Prove2me | Theorems.Thm_MultiwayCut_theorem_1_2
-- name    : MultiwayCut.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:16:45.073874+00:00
-- url     : https://prove2.me/theorems/3b04444c-f92e-455a-95b0-c783c22016a2
-- title:
--   Theorem 1.2 — exponential clocks mixed with CKR on the transformation (5.3) is a $297/229$-approximation for Multiway Cut
-- statement:
--   Theorem 1.2 states: "Using only the exponential clocks and CKR algorithms, it is possible to achieve an approximation of $297/229\approx1.29694$ for the Multiway Cut problem." The algorithm (§5.1, p.7) is Algorithm 3 with $p=\frac{121}{229}$ and the transformation (5.1) defined by the matrix (5.3).
--
--   Let $k\ge1$, let an instance be given (vertices $V$, edges $E$, weights $w_e\ge0$, distinct terminals $t_1,\dots,t_k$), and let $x$ be any feasible embedding of the simplex relaxation. Then:
--   1. **Feasibility.** With probability $1$, both the exponential-clocks branch and the CKR branch label every terminal $t_i$ by $i$.
--   2. **Against the relaxation.** The expected weight of the cut produced by the algorithm satisfies
--   $$\mathbb E[\mathrm{cut}]=\sum_{e=(u,v)\in E}w_e\Pr[g(x_u)\ne g(x_v)]\le\frac{297}{229}\sum_{e=(u,v)\in E}w_e\,\tfrac12\|x_u-x_v\|_1 .$$
--   3. **Against the optimum.** If $x$ is an optimal solution of the relaxation, then $\mathbb E[\mathrm{cut}]\le\frac{297}{229}\,\mathrm{cut}(g)$ for every feasible labeling $g$; in particular $\mathbb E[\mathrm{cut}]\le\frac{297}{229}\,\mathrm{OPT}$.
--
--   This is the paper's main theorem: a rounding scheme built from the two classical ingredients alone, applied after a sorted quadratic transformation of the simplex, matches the computer-assisted 1.2965 bound of Sharma and Vondrák up to $10^{-3}$.
--
--   Differences from the source:
--   - reading: "it is possible to achieve … using only the exponential clocks and CKR algorithms" → the explicit algorithm of §5.1: Algorithm 3 with $p=121/229$ and the transformation (5.1) with the matrix (5.3); reason: the paper proves the existence claim by this algorithm (§5.1, p.7)
--   - reading: "an approximation of 297/229" → terminals labelled correctly almost surely and expected cut weight at most $297/229$ times the relaxation objective, resp. any feasible cut when the embedding is optimal; no running time; reason: the paper's proof bounds only the expected cost and never analyzes running time
--   - generalization: a guarantee for the algorithm run on an optimal relaxation solution → clause 2 holds for every feasible embedding $x$; reason: clause 3 is the source's form and follows from clause 2 at an optimal $x$
--   - generalization: an undirected graph with weights $w:E\to\mathbb R^+$ → a finite set of ordered pairs (parallel copies and loops allowed) with weights $w_e\ge0$; reason: a graph is the special case listing each edge once; zero weights add nothing
--   - encoding: expected weight of the cut → $\sum_{e\in E}w_e\cdot\Pr[\text{endpoints separated}]$, probabilities as (outer) measures of events; reason: linearity of expectation
--   - encoding: $r\sim\mathrm{Unif}[0,1]$ and an independent uniform permutation $\sigma$ → $\frac1{k!}\sum_\sigma\lambda(\{r\in[0,1]:\dots\})$ with Lebesgue outer measure $\lambda$; reason: this is the product law written as an average over $\sigma$; Mathlib has no measurable structure on permutations
--   - encoding: the paper's coordinates and terminals $1,\dots,k$, $1/\ell$ → `Fin k` from $0$, $1/(\ell+1)$; reason: Lean convention; the same statement after the index shift
--   - reading: the matrix (5.3) printed with "…" for a general $k$ → `A53 k` for every $k\ge1$, defined by the entry formula (the top-left $k\times k$ block of the printed pattern); reason: the paper never restricts $k$; this is the only matrix consistent with the printed pattern
-- source:
--   Buchbinder, Schwartz & Weizman, Simplex Transformations and the Multiway Cut Problem, manuscript of Nov. 1, 2016, Theorem 1.2, p.2 (algorithm §5.1, p.7; proof p.8)

import Mathlib
import Definitions.Def_MultiwayCut_Instance
import Definitions.Def_MultiwayCut_ExpClocks
import Definitions.Def_MultiwayCut_CKR
import Definitions.Def_MultiwayCut_Algorithm3
import Definitions.Def_MultiwayCut_Transformation
import Definitions.Def_MultiwayCut_A53

open MeasureTheory

namespace MultiwayCut

/-- **Theorem 1.2**, Buchbinder, Schwartz & Weizman, *Simplex Transformations and the Multiway
Cut Problem*, manuscript of Nov. 1, 2016, p.2 (proof p.8): "Using only the exponential clocks
and CKR algorithms, it is possible to achieve an approximation of 297/229 ≈ 1.29694 for the
Multiway Cut problem." The algorithm (§5.1, p.7) is Algorithm 3 with `p = 121/229` and the
transformation (5.1) with the matrix (5.3).

For every `k ≥ 1`, every instance (finite `V`, edges `E`, weights `w ≥ 0` on `E`, distinct
terminals `t`) and every feasible point `x` of the simplex relaxation:
1. both branches of Algorithm 3 label every terminal `tᵢ` by `i` almost surely;
2. the expected weight of the cut is at most `297/229` times the relaxation objective at `x`;
3. if `x` is an optimal solution of the relaxation, the expected weight of the cut is at most
   `297/229` times the weight of the cut of every feasible labeling (so at most
   `297/229 · OPT`).

**Formalization Note.** Terminals are `Fin k`, 0-based. Probabilities are measures of events
(outer measures); the expected cut weight is `Σ_{e∈E} w_e · Pr[e cut]` (`alg3Cost`).
No running time is asserted: the paper analyzes none. -/
theorem theorem_1_2 {k : ℕ} [NeZero k] {V : Type} [Fintype V] (I : Instance V k)
    (x : V → Fin k → ℝ) (hx : IsFeasibleEmbedding I x) :
    (clockLaw k {Z | ∃ i : Fin k, expClock Z (x (I.t i)) ≠ i} = 0 ∧
      ckrProb (fun r σ => ∃ i : Fin k, ckr r σ (quadTransform (A53 k) (x (I.t i))) ≠ i) = 0) ∧
    alg3Cost I (121 / 229) (quadTransform (A53 k)) x ≤ 297 / 229 * relaxValue I x ∧
    (IsRelaxOptimal I x → ∀ g : V → Fin k, IsFeasibleLabeling I g →
      alg3Cost I (121 / 229) (quadTransform (A53 k)) x ≤ 297 / 229 * cutWeight I g) := by sorry

end MultiwayCut
