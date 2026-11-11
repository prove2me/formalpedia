-- Prove2me | Theorems.Thm_IteratedLP_Gaussian_lemma_7_4
-- name    : IteratedLP.Gaussian.lemma_7_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:21:31.581105+00:00
-- url     : https://prove2.me/theorems/1494078c-4f15-4101-92c4-ca638b687967
-- title:
--   Lemma 7.4 — finite active-count inequality $|F_{t-1}|\le|C_t|+|I^{\mathrm{act}}_t|$
-- statement:
--   Fix the matrix $A\in\mathbb R^{M\times N}$, the margin $\kappa_t$ and the iterate $x^{(t-1)}$ entering round $t$, with frozen set $B_{t-1}=\{j:|x^{(t-1)}_j|=1\}$ and entering free set $F_{t-1}=[N]\setminus B_{t-1}$. Suppose the strict-feasibility event holds: some point of the box $[-1,1]^N$ that agrees with $x^{(t-1)}$ on $B_{t-1}$ satisfies every row constraint strictly. Then, almost surely over $v_t\sim N(0,I_N)$, every optimizer $x^{(t)}$ of the round-$t$ LP satisfies
--   $$|F_{t-1}|\le|C_t|+|I^{\mathrm{act}}_t|,$$
--   where $C_t=\{j\in F_{t-1}:|x^{(t)}_j|=1\}$ and $I^{\mathrm{act}}_t=\{i\in[M]:u^{(t)}_i=\kappa_t\}$, $u^{(t)}=Ax^{(t)}$.
--
--   The inequality counts active constraints at the optimal vertex; with Lemma 6.5 it pins down the fraction of newly frozen coordinates.
--
--   Differences from the source:
--
--   - reading: on the strict-feasibility event → hypothesis: some y in the box with y_j = x^(t−1)_j on B_{t−1} has (Ay)_i > κ_t for every row; reason: for t ≥ 2 the previous iterate is such a point (κ_t < κ_{t−1}); for t = 1 it is the reserve point of [LSZ25]; the proof uses only this
--   - generalization: almost surely over v_t, for the Gaussian matrix A (M = ⌊αN⌋) and the realized entering iterate x^(t−1) of ITERATED-LP → for every deterministic matrix A of any size M × N, every margin κ_t and every entering vector x^(t−1) satisfying the hypothesis, ∀ᵐ v ∼ N(0, I_N), every x in optSet A v κ_t x^(t−1); reason: v_t is independent of (A, x^(t−1)), so applying the fixed-data form to the realized (A, x^(t−1)) and integrating (Fubini) gives the source's event form
-- source:
--   Zhang, Li, State Evolution and Universality of Iterated Linear Programs for the Binary Perceptron, arXiv:2611.04294v1, p. 38, Lemma 7.4

import Mathlib
import Definitions.Def_IteratedLP_Gaussian_Model

open MeasureTheory ProbabilityTheory

namespace IteratedLP.Gaussian

open scoped Classical in
/-- Lemma 7.4 (Finite active-count inequality, p. 38). Fix the matrix `A`, the margin `κ_t` and
the entering iterate `x^{(t-1)}` (frozen set `B_{t-1} = {j : |x^{(t-1)}_j| = 1}`, entering free
set `F_{t-1}` its complement). On the strict-feasibility event — some point of the entering box
with the frozen coordinates fixed satisfies every row constraint strictly — almost surely over
`v_t ∼ N(0, I_N)`, every optimizer `x^{(t)}` of the round-`t` LP satisfies
`|F_{t-1}| ≤ |C_t| + |I^act_t|`, where `C_t = {j ∈ F_{t-1} : |x^{(t)}_j| = 1}` and
`I^act_t = {i : u^{(t)}_i = κ_t}`, `u^{(t)} = A x^{(t)}`. -/
theorem lemma_7_4 (M N : ℕ) (A : Fin M → Fin N → ℝ) (κt : ℝ) (xprev : Fin N → ℝ)
    (hstrict : ∃ y ∈ feasibleSet A κt xprev, ∀ i, κt < ∑ j, A i j * y j) :
    ∀ᵐ v ∂(stdGaussVec N), ∀ x ∈ optSet A v κt xprev,
      (Finset.univ.filter (fun j => |xprev j| ≠ 1)).card ≤
        (Finset.univ.filter (fun j => |xprev j| ≠ 1 ∧ |x j| = 1)).card +
          (Finset.univ.filter (fun i => ∑ j, A i j * x j = κt)).card := by sorry

end IteratedLP.Gaussian
