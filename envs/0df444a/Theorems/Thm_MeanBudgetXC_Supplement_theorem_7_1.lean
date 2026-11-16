-- Prove2me | Theorems.Thm_MeanBudgetXC_Supplement_theorem_7_1
-- name    : MeanBudgetXC.Supplement.theorem_7_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:17:26.793623+00:00
-- url     : https://prove2.me/theorems/bf3269ba-2d34-4013-96ad-71f84bdd7679
-- title:
--   Theorem 7.1 — finite rational grids $\Gamma_{\lceil M/e_\theta\rceil}$ and $\Gamma_{\lceil M/(e_\theta\tau)\rceil}$ still force $2^{\Omega_\theta(N^\kappa)}$ inequalities
-- statement:
--   Notation. Write $M=\binom N2$ for the number of pair coordinates $q_{ij}$ ($i<j$), $P^{(a)}_{N,d}$ for the pair body of consistent local laws on all contexts of size at most $d$ with at most $a$ ones, and $P^{(a;B)}_{N,d}$ for its subset of arrays coming from a system with mean budget $\sum_ip_i\le B$; $P=P^{(2)}_{N,d}$ and $P_B=P^{(2;B)}_{N,d}$. For a set $A$ of pair arrays and a cap $u\ge0$, the **capped value** is
--   $$V_A(u)=\max\{1^{\mathsf T}q:\ q\in A,\ 0\le q\le u\}.$$
--   A **common LP** is a linear system with $s$ inequalities (equations and auxiliary variables free, real coefficients) projecting onto an output polyhedron $K$; it is fixed before the cap, each query adds the cap $0\le q\le u$ directly on the output, and its error at $u$ is $|V_K(u)-V_{\text{target}}(u)|$ (Section 1.3).
--
--   For an integer $L\ge1$ let $\Gamma_L=\{0,1/L,\dots,1\}$. There is an absolute $\kappa>0$ (the exponent of Theorem 5.2) such that for every $\theta\in(0,1)$, with $d=\lfloor\theta N\rfloor$, there are a rational $e_\theta>0$, a constant $c>0$ and a threshold $N_0$ with the following property for every $N\ge N_0$ and every $a\ge2$:
--
--   | target | grid denominator | total error |
--   |---|---|---|
--   | $P^{(a)}_{N,d}$ | $L_0=\lceil M/e_\theta\rceil$ | $e_\theta$ |
--   | $P^{(a;B)}_{N,d}$, $B>2$ | $L_B=\lceil M/(e_\theta\tau)\rceil$ | $e_\theta\tau$, $\tau=\min\{B-2,1\}$ |
--
--   any common LP whose capped feasible sets are nonempty at every cap in $\Gamma^M_{L}$ and whose error is at most the listed tolerance at every cap in $\Gamma^M_{L}$ (for the listed $L$) has at least $2^{cN^\kappa}$ inequalities. The size threshold and constants are independent of $a$ and $B$.
--
--   The lower bounds of the paper therefore do not depend on real-valued capacities: a grid with $O_\theta(N^2)$ symbols (for fixed surplus) suffices.
--
--   Differences from the source:
--   - encoding: the vertex set $[N]$ → `Fin N`; reason: the same set, indexed from zero
--   - encoding: a common LP (base formulation) with $s$ inequalities and output polyhedron $K$ → `IsEFOfSize K s` (platform); reason: the paper's counting convention (p.4, App. A.1): inequalities counted, equations and auxiliary variables free, real coefficients, unbounded lifts allowed
--   - encoding: $V_A(u)=\max\{1^{\mathsf T}q: q\in A,\ 0\le q\le u\}$ → `capValue A u`, the supremum of $\sum_e q_e$ over the capped set; reason: the capped set is nonempty and lies in the box $[0,u]$, and $A$ is a polyhedron or a compact body, so the supremum is attained and equals the maximum
--   - encoding: nonempty capped feasible sets and finite values → nonempty capped sets only; reason: the capped set lies in the box $[0,u]$, so the value is always finite; the finiteness hypothesis excludes nothing
--   - reading: $\kappa$ is the exponent of Theorem 5.2 → an absolute $\kappa>0$ quantified first, before every other constant; reason: each statement is standalone; Theorem 5.2 fixes $\kappa$ only as an absolute positive constant
--   - reading: needs $2^{\Omega_\theta(N^\kappa)}$ inequalities; "the size threshold and rank constants are independent of $a,B$" → a constant $c>0$ and a threshold $N_0$ depending on $\theta$ only, chosen with $e_\theta$ before $N$, $a$, $B$ and the LP, with $2^{cN^\kappa}\le s$; reason: this is the stated dependence
--   - encoding: $\lceil\cdot\rceil$ of a real quotient → `Nat.ceil`; reason: the quotients are positive for $N\ge2$
-- source:
--   Chao–Gao–Qi–Wang, A Sharp Mean-Budget Transition for Local Pair Marginals, STOC 2027 submission (manuscript sha256 882d9c712270634eb9c25e965df506f4fd2cfa5c228f4bb13f3ca9ddc9859e76), Theorem 7.1, pp.35–36

import Mathlib
import Definitions.Def_ExtensionComplexity_TSP_extensionComplexity
import Definitions.Def_MeanBudgetXC_pairBody
import Definitions.Def_MeanBudgetXC_budgetBody
import Definitions.Def_MeanBudgetXC_Supplement_IsGridCap
import Definitions.Def_MeanBudgetXC_Supplement_capValue

namespace MeanBudgetXC.Supplement

open ExtensionComplexity.TSP

/-- **Theorem 7.1** (Finite rational queries) (Chao–Gao–Qi–Wang, *A Sharp Mean-Budget Transition for Local Pair Marginals*, STOC 2027
submission, manuscript sha256 882d9c71…9e76, Theorem 7.1, pp.35–36). Fix
`θ ∈ (0, 1)`, `d = ⌊θN⌋`, and `M = (N choose 2)`. There is a rational `e_θ > 0` such that, for every
`a ≥ 2`, any common LP with nonempty capped feasible sets and finite values on the listed grid, and
error at most the listed tolerance, needs `2^{Ω_θ(N^κ)}` inequalities:
target `P^{(a)}_{N,d}`, grid denominator `L₀ = ⌈M/e_θ⌉`, total error `e_θ`;
target `P^{(a;B)}_{N,d}`, `B > 2`, grid denominator `L_B = ⌈M/(e_θ τ)⌉`, total error `e_θ τ`,
`τ = min{B − 2, 1}`. The queries are all vectors in `Γ^M_{L₀}` or `Γ^M_{L_B}`. The size threshold
and rank constants are independent of `a, B`. The common LP conventions of Section 1.3 apply on
this grid.

**Formalization Note** `κ` is the absolute exponent of Theorem 5.2, chosen first. `2^{Ω_θ(N^κ)}`
is read as a constant `c > 0` and a threshold `N₀` depending on `θ` only, chosen with `e_θ` before
`N`, `a`, `B` and the LP. The LP is `IsEFOfSize K s` with `K` arbitrary (Section 1.3 conventions);
its hypotheses are imposed only on the grid caps. Finite values are automatic, so only nonemptiness
is assumed. `⌈·⌉` is `Nat.ceil`. -/
theorem theorem_7_1 :
    ∃ κ : ℝ, 0 < κ ∧ ∀ θ : ℝ, 0 < θ → θ < 1 →
      ∃ eθ : ℚ, 0 < eθ ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a : ℕ, 2 ≤ a →
        (∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
          (∀ u : Pair (Fin N) → ℝ, IsGridCap ⌈(N.choose 2 : ℝ) / eθ⌉₊ u →
            (cappedSet K u).Nonempty) →
          (∀ u : Pair (Fin N) → ℝ, IsGridCap ⌈(N.choose 2 : ℝ) / eθ⌉₊ u →
            |capValue K u - capValue (pairBody (Fin N) ⌊θ * N⌋₊ a) u| ≤ eθ) →
          (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s) ∧
        ∀ B : ℝ, 2 < B →
          ∀ (K : Set (Pair (Fin N) → ℝ)) (s : ℕ), IsEFOfSize K s →
            (∀ u : Pair (Fin N) → ℝ, IsGridCap ⌈(N.choose 2 : ℝ) / (eθ * min (B - 2) 1)⌉₊ u →
              (cappedSet K u).Nonempty) →
            (∀ u : Pair (Fin N) → ℝ, IsGridCap ⌈(N.choose 2 : ℝ) / (eθ * min (B - 2) 1)⌉₊ u →
              |capValue K u - capValue (budgetBody (Fin N) ⌊θ * N⌋₊ a B) u| ≤
                eθ * min (B - 2) 1) →
            (2 : ℝ) ^ (c * (N : ℝ) ^ κ) ≤ s := by sorry

end MeanBudgetXC.Supplement
