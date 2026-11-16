-- Prove2me | Theorems.Thm_LocalPush_Supplement_theorem_5_11
-- name    : LocalPush.Supplement.theorem_5_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:19:35.256241+00:00
-- url     : https://prove2.me/theorems/542d2222-af85-4b7b-a350-1c31aba100a6
-- title:
--   Theorem 5.11 — $\ell_1$-regularized PageRank: $\xi$-approximate minimizer supported in $S^*$, in time $\tilde O(\min\{1/(\sqrt\alpha\rho),1/\rho^2\})$ (corrected: additive constant in the time bounds)
-- statement:
--   Let $G=(V,E)$ be a finite simple undirected graph without isolated nodes, given by adjacency lists in any order, with degree matrix $D$ and degree vector $d$. For a seed $s$, $\alpha\in(0,1)$ and $\rho>0$, the $\ell_1$-regularized PageRank objective (eq. (2)) is
--   $$\psi_\rho(x)=\tfrac12x^\top\big(D-(1-\alpha)A\big)x-\alpha x(s)+\alpha\rho\|Dx\|_1 .$$
--   Let $x^*$ be its minimizer over $\mathbb R^V$ and $S^*=\mathrm{supp}(x^*)$.
--
--   There are a program $P$ of the base randomized real RAM, a constant $C>0$ and an exponent $k$ such that for every such graph, seed $s$, $\alpha\in(0,1)$, $\rho>0$, $\xi>0$ and $\delta\in(0,1)$, with probability at least $1-\delta$ over the coins the run of $P$ on input $(s,\alpha,\rho,\xi,\delta)$ halts with an output $\tilde x$ such that
--
--   1. $\tilde x\ge0$ and $\psi_\rho(\tilde x)-\psi_\rho(x^*)\le\xi$;
--   2. $D\tilde x$ is an ACL $(2\rho)$-approximate PageRank vector for the seed $s$;
--   3. $\mathrm{supp}(\tilde x)\subseteq S^*$ and $\mathrm{vol}(\mathrm{supp}(\tilde x))\le1/\rho$;
--   4. the running time is at most both
--   $$C\Big(1+\min\Big\{\frac1{\sqrt\alpha\,\rho},\frac1{\rho^2}\Big\}\mathrm L\Big(\frac1{\alpha\rho\xi\delta}\Big)^k\Big)\quad\text{and}\quad C\Big(1+\min\Big\{|S^*|,\frac1{\sqrt\alpha}\Big\}\widetilde{\mathrm{vol}}(S^*)\,\mathrm L\Big(\frac1{\alpha\rho\xi\delta}\Big)^k+|S^*|\,\mathrm{vol}(S^*)\Big),$$
--   where $\mathrm L(x)=\max\{1,\log x\}$ and $\widetilde{\mathrm{vol}}(S)=|S|+|\{\{u,v\}\in E:u,v\in S\}|$.
--
--   All clauses hold together on one event. The result adapts ActiveSetPush to the sparse optimization view of PageRank and removes a factor $|S^*|$ from the first term of the earlier deterministic bound of the ASPR algorithm.
--
--   **Formalization Note** $x^*$ is quantified as any minimizer of $\psi_\rho$; the paper states it is unique. The program receives only $s,\alpha,\rho,\xi,\delta$.
--
--   Differences from the source:
--   - correction: running time O(min{1/(√α ρ), 1/ρ²} polylog(1/(αρξδ))) and O(min{|S∗|, 1/√α} vol~(S∗) polylog(1/(αρξδ)) + |S∗| vol(S∗)) → work ≤ C·(1 + min{1/(√α ρ), 1/ρ²}·L(1/(αρξδ))^k) and work ≤ C·(1 + min{|S∗|, 1/√α}·vol~(S∗)·L(1/(αρξδ))^k + |S∗|·vol(S∗)); reason: the second printed bound is false: if ρ d(s) ≥ 1 then 0 satisfies the optimality condition of ψ_ρ, so x∗ = 0, S∗ = ∅ and the bound is O(0), while every run takes at least one step; the additive 1 changes nothing else
--   - reading: polylog(1/(αρξδ)) and O(·) → L(1/(αρξδ))^k with L = clog = max{1, log} and k, C chosen with the program before the graph and all parameters; reason: the usual meaning of polylog and O with a constant uniform in α (p.4: α is not a constant), as in the published goal
--   - reading: "there exists an algorithm" with a running time → one admissible program of the base machine LocalPush.Machine; running time = its work counter; reason: the paper names only the adjacency-list query model; same reading as the published goal Theorem 1.2
--   - reading: satisfies the following properties with probability at least 1 − δ → a measurable set of fair-coin tapes of probability ≥ 1 − δ on which the run halts and all clauses and both time bounds hold; reason: both bullets sit under the one probability as printed
--   - encoding: x∗ the unique minimizer of ψ_ρ → every xstar with ψ_ρ(xstar) ≤ ψ_ρ(y) for all y; reason: the minimizer exists and is unique (ψ_ρ is strictly convex for α ∈ (0, 1) without isolated nodes), so this is the same object
--   - encoding: a graph, a returned vector x̃ → adjacency lists satisfying IsAdjList; input layout l1Input; x̃(v) is real memory at −1 − v; reason: a fixed representation of the same instances; the program is not given n, m or the lists
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.3, Theorem 5.11, p.27 (PDF p.27); ψ_ρ, eq. (2), p.5; internal volume, p.27

import Mathlib
import Definitions.Def_LocalPush_PageRank
import Definitions.Def_LocalPush_ResidueSystem
import Definitions.Def_LocalPush_Layout
import Definitions.Def_LocalPush_Supplement_Inputs
import Definitions.Def_LocalPush_Supplement_Spectral

open Finset Matrix

namespace LocalPush

namespace Supplement

/-- **Theorem 5.11 (ℓ₁-regularized PageRank) (corrected: additive constant in the running-time bounds).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.3, Theorem 5.11, p.27
(PDF p.27); `ψ_ρ` is eq. (2), p.5.

"Given a seed node s ∈ V, α ∈ (0, 1), ρ > 0, ξ > 0, and δ ∈ (0, 1), let x∗ be the unique minimizer of ψρ(·)
and S∗ := supp(x∗). There exists an algorithm that satisfies the following properties with probability at
least 1 − δ: • it returns x̃ ≥ 0 such that ψρ(x̃) − ψρ(x∗) ≤ ξ, Dx̃ is an ACL (2ρ)-approximate PageRank
vector, supp(x̃) ⊆ S∗, and vol(supp(x̃)) ≤ 1/ρ; • its running time is bounded by both
O(min{1/(√α ρ), 1/ρ²} polylog(1/(αρξδ))) and
O(min{|S∗|, 1/√α} vol~(S∗) polylog(1/(αρξδ)) + |S∗| vol(S∗))."

There are an admissible program `P` of the base machine, a constant `C > 0` and an exponent `k` such that for
every graph given by adjacency lists (`IsAdjList`), every seed `s`, all `α ∈ (0, 1)`, `ρ, ξ > 0`,
`δ ∈ (0, 1)` and every minimizer `x*` of `ψ_ρ`, some measurable set of coin tapes of probability at least
`1 − δ` has, on each of its tapes, a halting step `t` of the run on input `(s, α, ρ, ξ, δ)` whose output
`x̃` satisfies all five output clauses and whose work satisfies both running-time bounds.

**Formalization Note.**
* `polylog(X)` is `L(X)^k` with `L = clog = max{1, log}` and `k` chosen with `P` and `C`, before the
  instance; `C` is uniform in all parameters.
* Correction: each running-time bound is read as `C·(1 + ·)`. For `ρ d(s) ≥ 1` the minimizer is `x* = 0`
  (`0` satisfies the optimality condition of `ψ_ρ`), so `S* = ∅` and the second printed bound is `O(0)`,
  while every halting run takes at least one step.
* `x*` is any minimizer of `ψ_ρ` over `ℝ^V`; the paper asserts it is unique (`ψ_ρ` is strictly convex for
  `α ∈ (0, 1)` without isolated nodes), and nothing else is assumed about it. -/
theorem theorem_5_11 :
    ∃ P : Program, Admissible P ∧ ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
      ∀ (n : ℕ) (nbrs : Fin n → List (Fin n)), IsAdjList nbrs →
      ∀ (s : Fin n) (α ρ ξ δ : ℝ), 0 < α → α < 1 → 0 < ρ → 0 < ξ → 0 < δ → δ < 1 →
      ∀ xstar : Fin n → ℝ, (∀ y, psi (toGraph nbrs) s α ρ xstar ≤ psi (toGraph nbrs) s α ρ y) →
        ∃ E : Set (ℕ → Bool), MeasurableSet E ∧ ENNReal.ofReal (1 - δ) ≤ coinTape E ∧
          ∀ ω ∈ E, ∃ t : ℕ,
            (run P nbrs (l1Input s α ρ ξ δ) ω t).halted = true ∧
            (∀ v, 0 ≤ outVec n (run P nbrs (l1Input s α ρ ξ δ) ω t) v) ∧
            psi (toGraph nbrs) s α ρ (outVec n (run P nbrs (l1Input s α ρ ξ δ) ω t)) -
              psi (toGraph nbrs) s α ρ xstar ≤ ξ ∧
            IsACL (toGraph nbrs) α (e s) (2 * ρ)
              (degM (toGraph nbrs) *ᵥ outVec n (run P nbrs (l1Input s α ρ ξ δ) ω t)) ∧
            supp (outVec n (run P nbrs (l1Input s α ρ ξ δ) ω t)) ⊆ supp xstar ∧
            vol (toGraph nbrs) (supp (outVec n (run P nbrs (l1Input s α ρ ξ δ) ω t))) ≤ 1 / ρ ∧
            ((run P nbrs (l1Input s α ρ ξ δ) ω t).work : ℝ) ≤
              C * (1 + min (1 / (Real.sqrt α * ρ)) (1 / ρ ^ 2) * clog (1 / (α * ρ * ξ * δ)) ^ k) ∧
            ((run P nbrs (l1Input s α ρ ξ δ) ω t).work : ℝ) ≤
              C * (1 + min ((supp xstar).card : ℝ) (1 / Real.sqrt α) *
                  volInt (toGraph nbrs) (supp xstar) * clog (1 / (α * ρ * ξ * δ)) ^ k +
                ((supp xstar).card : ℝ) * vol (toGraph nbrs) (supp xstar)) := by sorry

end Supplement

end LocalPush
