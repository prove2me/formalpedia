-- Prove2me | Theorems.Thm_MinorFreeSTC_Main_theorem_9
-- name    : MinorFreeSTC.Main.theorem_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:20:49.687395+00:00
-- url     : https://prove2.me/theorems/cb8c8426-fe32-4e26-a75c-f0c1427d9582
-- title:
--   Theorem 9 — separated neighborhood covers give (1+ϵ)-distortion γ-growing centered hierarchy covers of size τ·(O(1/ϵ))^r·log γ w.h.p.
-- statement:
--   Let $c_0\ge1$ be a constant of Corollary 1. There is a universal constant $c>0$ such that the following holds. Let $G$ be a connected $n$-vertex $K_r$-minor-free weighted graph (weights in $[1,n^k]$) and fix $\alpha,\tau\ge1$, $s>0$. **(E)** If for every $\Delta>0$ there is a $\tau$-size, $\alpha$-padded, $\Delta$-diameter, $s$-separated neighborhood cover of $G$, then for every $\epsilon\in(0,1)$ and
--   $$\gamma\ \ge\ \max\Big\{2+\frac1s,\ 4,\ \frac{32c_0\alpha r\log_2n}{\epsilon}\Big\}$$
--   there is a $(1+\epsilon)$-distortion $\gamma$-growing centered hierarchy cover $\mathcal F$ of $G$ with $|\mathcal F|\le\tau\,(c/\epsilon)^r\log_2\gamma$. **(A)** For every $c'>1$ one admissible oracle program, for all $r,k,\alpha,\tau,s,\epsilon$ with constants $C,K$, given $(G,\epsilon,\gamma,r,\alpha,\tau,s)$ and an oracle answering every query $\Delta>0$ with such a cover, outputs such an $\mathcal F$ within $C(n+\log_2\gamma)^K+C$ steps, failing with coin-tape measure at most $n^{-c'}$.
--
--   With Theorem 10 this reduces spanning tree covers to separated neighborhood covers (Lemma 24).
--
--   Differences from the source:
--   - reading: 'Suppose that, for every ∆ > 0, we can construct a … cover. Then … we can, with high probability, construct … If the separated neighborhood covers can be constructed in polynomial time, then so can …' → (E) if for every ∆ > 0 such a cover exists, the conclusion's object exists; (A) a black-box reduction: one admissible oracle program which, with an oracle returning some valid such cover for every query ∆ > 0 (an arbitrary such oracle), runs within the stated step bound counting one step per oracle call and fails with coin-tape measure ≤ n^{−c}; reason: the conditional statement has an existence and an algorithmic reading; the black-box reading is what the proof does and is stronger than 'poly-time oracle implies poly-time'; one step per call is equivalent to one step per output cell since an answer has at most ⌊τ⌋·n + 1 cells and C may depend on τ
--   - reading: 'where c0 ≥ 1 is the universal constant from Corollary 1' → hypotheses 1 ≤ c₀ and `CopConstant c₀`; the conclusion for every such c₀; reason: names 'the constant of Corollary 1' without choosing one
--   - reading: 'construct in polynomial time' with γ part of the input → step bound C·(n + log₂ γ)^K + C, C, K depending on r, k, α, τ, s, ϵ, c' (the parameters the statement fixes); reason: the output has τ(O(1/ϵ))^r log γ hierarchies, so its size grows with log γ; log γ is the bit length of γ
--   - reading: (O(1/ϵ))^r → one explicit existentially quantified universal constant, chosen before every other quantity; reason: p. 13: O(·) has universal hidden constants unless otherwise stated
--   - encoding: graph (with the standing assumption 'we will assume all input graphs are connected', p. 14) → hypothesis `Connected G` (d_G(u, v) < ∞ for all u, v); reason: standing assumption of §3.1 made explicit
--   - encoding: 'we will assume … w(e) ∈ [1, poly(n)]' (p. 13, standing for §§4–9.1) → hypothesis `AspectBounded G k` (1 ≤ w(e) ≤ n^k) for an arbitrary k : ℕ; running-time constants may depend on k; reason: standing assumption of §3.1 made explicit; §9.2 removes it only for the final theorem
--   - encoding: n-node graph → `[Nonempty V]` (n ≥ 1); reason: log n, log log n and n^{−c} are undefined or degenerate at n = 0
--   - encoding: log → `Real.logb 2` (Lean's `logb 2 0 = 0` gives log 0 a value at n = 1); reason: p. 13: all logarithms are base 2
--   - encoding: distances d_G, d_C, d_T and α·d_G(u, v) → values in [0, ∞] (`ℝ≥0∞`), α·d as `ENNReal.ofReal α * d`; reason: the published `WGraph.dist`/`distIn` convention; on connected graphs and connected clusters every distance is finite
--   - encoding: a collection (of trees / partial partitions / hierarchies) of size k → a family indexed by `Fin k` (repetitions allowed), size bound on k; reason: a repeated member can be dropped, so 'at most k members' is the same class
--   - encoding: the graph (and parameters) given to the algorithm; its output → input cells `E.cells` ([n, m, then each listed edge as endpoint numbers and weight], for every enumeration and edge order `E : Encoding G`) followed by the parameters; output read from the memory block named by pointers p[1], p[2] in the layout of the corresponding `…Out` predicate; reason: a machine needs a concrete layout; quantifying over every encoding means the algorithm cannot exploit a convenient order
-- source:
--   Filtser, Fletcher, Hershkowitz, Milenković, (1 + ϵ)-Distortion Spanning Tree Covers of Minor-Free Graphs with Size O(log log n), STOC 2027 submission (manuscript sha256 f475e254…), p. 29, Theorem 9

import Mathlib
import Definitions.Def_ARTreeCover_WGraph
import Definitions.Def_MinorFreeSTC_Main_Graphs
import Definitions.Def_MinorFreeSTC_Main_Covers
import Definitions.Def_MinorFreeSTC_Main_Machine
import Definitions.Def_MinorFreeSTC_Main_CopConstant

set_option autoImplicit false

open scoped ENNReal

namespace MinorFreeSTC.Main

open ARTreeCover

/-- **Theorem 9** (Centered Hierarchy Covers, p. 29). Let `c₀ ≥ 1` be a constant of Corollary 1.
There is a universal `c` such that for every connected `K_r`-minor-free weighted graph and
`α, τ ≥ 1`, `s > 0`: **(E)** if for every `∆ > 0` there is a `τ`-size, `α`-padded, `∆`-diameter,
`s`-separated neighborhood cover, then for every `ϵ ∈ (0, 1)` and
`γ ≥ max{2 + 1/s, 4, 32c₀αr log n/ϵ}` there is a `(1 + ϵ)`-distortion `γ`-growing centered
hierarchy cover of size at most `τ (c/ϵ)^r log γ`; **(A)** for every `c' > 1` one oracle program,
given such covers by an oracle answering every `∆ > 0`, computes such a hierarchy cover in
`C (n + log γ)^K + C` steps (one step per oracle call) with failure probability `≤ n^{−c'}`. -/
theorem theorem_9 (c₀ : ℝ) (hc₀ : 1 ≤ c₀) (hcop : CopConstant c₀) :
    ∃ c : ℝ, 0 < c ∧
      (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (r k : ℕ)
        (α τ s : ℝ),
        Connected G → MinorFree G r → AspectBounded G k → 1 ≤ α → 1 ≤ τ → 0 < s →
        (∀ Δ : ℝ, 0 < Δ → ∃ (m : ℕ) (𝒞 : Fin m → Finset (Finset V)), IsSepCover G m 𝒞 τ α Δ s) →
        ∀ ϵ γ : ℝ, 0 < ϵ → ϵ < 1 →
          max (max (2 + 1 / s) 4) (32 * c₀ * α * r * Real.logb 2 (Fintype.card V) / ϵ) ≤ γ →
          ∃ (m : ℕ) (F : Fin m → Hierarchy V),
            IsCenteredHierarchyCover G m F (1 + ϵ) γ ∧ (m : ℝ) ≤ τ * (c / ϵ) ^ r * Real.logb 2 γ) ∧
      ∀ c' : ℝ, 1 < c' → ∃ A : Program, Admissible A ∧
        ∀ (r k : ℕ) (α τ s ϵ : ℝ), 1 ≤ α → 1 ≤ τ → 0 < s → 0 < ϵ → ϵ < 1 → ∃ C K : ℝ,
          ∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : WGraph V) (γ : ℝ)
            (E : Encoding G) (O : Oracle),
            Connected G → MinorFree G r → AspectBounded G k →
            max (max (2 + 1 / s) 4) (32 * c₀ * α * r * Real.logb 2 (Fintype.card V) / ϵ) ≤ γ →
            (∀ Δ : ℝ, 0 < Δ → CoverOut E (fun m 𝒞 => IsSepCover G m 𝒞 τ α Δ s) (O Δ)) →
            ComputesWHP A O (E.cells ++ [ϵ, γ, (r : ℝ), α, τ, s])
              (HierarchiesOut E fun m F =>
                IsCenteredHierarchyCover G m F (1 + ϵ) γ ∧ (m : ℝ) ≤ τ * (c / ϵ) ^ r * Real.logb 2 γ)
              (C * ((Fintype.card V : ℝ) + Real.logb 2 γ) ^ K + C)
              ((Fintype.card V : ℝ) ^ (-c')) := by sorry

end MinorFreeSTC.Main
