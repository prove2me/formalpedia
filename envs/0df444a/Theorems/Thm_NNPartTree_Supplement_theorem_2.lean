-- Prove2me | Theorems.Thm_NNPartTree_Supplement_theorem_2
-- name    : NNPartTree.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:11:22.712991+00:00
-- url     : https://prove2.me/theorems/efbc866a-b8d5-484b-adcf-ac8a1fb664d9
-- title:
--   Theorem 2 — NP-hardness of proper balanced halfspace cuts
-- statement:
--   For pairs $(x_1, y_1), \dots, (x_m, y_m)$ in $\mathbb{R}^d \times \mathbb{R}^d$, let $\mathcal{D}$ be the uniform distribution over $\{(x_i, y_i)\}_{i=1}^m$. For a cut $f : \mathbb{R}^d \to \{-1, 1\}$ write $\mathrm{err}_{\mathcal D}(f) = \Pr_{(x,y) \sim \mathcal D}[f(x) \ne f(y)]$ and $\mathrm{bal}_{\mathcal D}(f) = \min\{\Pr_{y \sim \mathcal D_Y}[f(y) = 1], \Pr_{y \sim \mathcal D_Y}[f(y) = -1]\}$, and let $\mathcal{P}_1$ be the class of halfspaces $f(x) = \mathrm{sign}(\langle h, x\rangle - \theta)$ with $\mathrm{sign}(0) = 1$.
--
--   **Theorem.** There is a universal constant $c > 0$ such that for every $\beta \in (0, 1/2]$ it is NP-hard to distinguish between the cases
--
--   1. there is $f \in \mathcal{P}_1$ with $\mathrm{bal}_{\mathcal D}(f) = 1/2$ and $\mathrm{err}_{\mathcal D}(f) = 0$;
--   2. every $f \in \mathcal{P}_1$ with $\mathrm{bal}_{\mathcal D}(f) \ge \beta$ satisfies
--   $$\mathrm{err}_{\mathcal D}(f) \ge c\,\beta.$$
--
--   That is, every NP language reduces in polynomial time to the problem: members map to instances of the first kind and non-members to instances of the second kind. The constant $c$ does not depend on $\beta$.
--
--   The theorem shows that no polynomial-time *proper* learner can output a halfspace whose error is within any multiplicative factor, or within a small additive constant, of the optimal balanced halfspace cut (unless P = NP). This is why the paper's learner (Theorem 3) is improper and outputs low-degree polynomial threshold functions.
--
--   **Formalization Note** NP-hardness of the distinguishing problem is the published `GapNPHard` (Karp reductions computed by Cook's one-tape Turing machines, from every NP language over every finite nonempty alphabet). Instances are `CutInstance`s: $d$ and $m$ unbounded, rational pairs listed with multiplicity, in the binary encoding `CutInstance.enc`. The reduction may depend on $\beta$.
--
--   Differences from the source:
--   - encoding: pairs in ℝ^d × ℝ^d → rational pairs given in the binary encoding CutInstance.enc (numerator and denominator in binary); reason: a polynomial-time reduction outputs finite strings, and every rational instance is an instance of the printed problem, so hardness on rational instances is hardness of the printed problem
--   - reading: "NP-hard" (no machine model or reduction type named) → GapNPHard: polynomial-time Karp reductions on Cook's one-tape Turing machines from every NP language over every finite nonempty alphabet, members to case 1 and non-members to case 2; reason: the standard meaning of NP-hardness of a distinguishing (promise) problem
--   - encoding: the uniform distribution over the m pairs → the empirical law of the list, with both cases also requiring m ≥ 1; reason: the uniform distribution over an empty list is undefined; the guard only excludes that case
-- source:
--   Khanna, Padaki, Waingarten, Learning Partition Trees for Nearest Neighbor Search, arXiv:2607.09909 (held copy of 2026-11-03, sha256 d32992f2…), Theorem 2, p.11 (PDF p.11)

import Mathlib
import Definitions.Def_SetCoverThreshold_SetCover_Complexity
import Definitions.Def_NNPartTree_Supplement_CutInstance

set_option autoImplicit false

namespace NNPartTree.Supplement

open SetCoverThreshold.SetCover

/-- **Theorem 2** (hardness of proper learning) (Khanna–Padaki–Waingarten, *Learning Partition Trees
for Nearest Neighbor Search*, arXiv:2607.09909, held copy of 2026-11-03, sha256 d32992f2…, Theorem 2,
p.11, PDF p.11).
There is a universal constant `c > 0` such that for every `β ∈ (0, 1/2]` it is NP-hard to distinguish,
given pairs `(x₁, y₁), …, (x_m, y_m)` in `ℝᵈ × ℝᵈ` with `D` the uniform distribution over them,
* some halfspace `f ∈ P₁` has `bal_D(f) = 1/2` and `err_D(f) = 0`, from
* every halfspace `f ∈ P₁` with `bal_D(f) ≥ β` has `err_D(f) ≥ c β`.

**Formalization Note** "NP-hard to distinguish" is the published `GapNPHard`: every NP language over
every finite nonempty alphabet has a polynomial-time Karp reduction (Cook's one-tape machines) to
instances in `Yes` (members) and in `No c β` (non-members). Instances are rational, with `d` and `m`
unbounded and pairs listed with multiplicity, in the binary encoding `CutInstance.enc`. `c` is chosen
before `β`; the reduction may depend on `β`. Halfspaces are the base `IsHalfspace` (`h = 0` allowed,
`sign(0) = 1`), with `err` and `bal` of the base mission. -/
theorem theorem_2 :
    ∃ c : ℝ, 0 < c ∧ ∀ β : ℝ, β ∈ Set.Ioc (0 : ℝ) (1 / 2) →
      GapNPHard CutInstance.enc CutInstance.Yes (CutInstance.No c β) := by sorry

end NNPartTree.Supplement
