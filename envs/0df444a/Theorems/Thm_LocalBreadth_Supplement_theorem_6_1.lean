-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_6_1
-- name    : LocalBreadth.Supplement.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:24:38.040199+00:00
-- url     : https://prove2.me/theorems/2a9ea548-31e9-457f-811b-e0d5a94a264d
-- title:
--   Theorem 6.1 — failure of simultaneous optimality in dimension $d\ge2$, with gap $c=1/16$
-- statement:
--   For every $d\ge2$ there is a countable family $\mathcal X$ of infinite languages in $\mathbb N^d\subseteq\mathbb Z^d$ such that, for every admissible threshold $h$ and every generator $G$ eventually valid on $\mathcal X$, some language $L\in\mathcal X$ satisfies
--   $$\beta_{G,h}(L)\le\beta_h(L)-\tfrac1{16}.$$
--
--   Here $h$ is admissible if it is positive, finite-valued and nondecreasing on $\mathbb N_{\ge1}$ with $\sup_N N/h(N)=\infty$; $\beta_{G,h}(L)$ is the density $G$ guarantees at $L$ and $\beta_h(L)$ the best density any eventually valid generator guarantees at $L$. In dimension one the per-target optima are attained simultaneously (Theorem 1.5); this theorem shows that in higher dimensions one generator can lose a fixed amount at some target, uniformly over thresholds.
--
--   Differences from the source:
--   - reading: "generator" / "eventually valid generator" (the theorem names only validity) → a generator that is fresh (IsFresh…) and universally eventually valid on the family; reason: the model conventions (p.13, used in Part II by p.51) require the global freshness condition o_t ∉ S_t ∪ O_{t−1} of every generator throughout the paper
--   - reading: infinite languages in ℕ^d (the universe of outputs is not named in §6) → languages are Set (Fin d → ℤ) whose points all have nonnegative coordinates, and generators output points of ℤ^d; reason: Definition 1.4 takes A, B ⊆ ℤ^d, and Part II lets the generator output anywhere in ℤ^d (Lemma 9.2); ℕ^d is the subset of ℤ^d with nonnegative coordinates
--   - encoding: h : ℕ_{≥1} → (0, ∞) → h : ℕ → ℝ with positivity and monotonicity required on n ≥ 1 only; reason: δ_h evaluates h only at volumes V(R) ≥ 1, so the value h 0 is never used
--   - encoding: a constant c = 1/16 → the literal 1/16; reason: the theorem fixes c = 1/16
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §6, Theorem 6.1, p.42 (PDF p.44)

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_betaH

namespace LocalBreadth.Supplement

/-- Theorem 6.1 (failure of simultaneous optimality in dimension `d ≥ 2`). Kleinberg, Wei, STOC 2027
submission (manuscript sha256 f924cbfc…), §6, p.42. For every `d ≥ 2` there exist a countable family
`X` of infinite languages in `ℕ^d` and the constant `c = 1/16` such that, for every admissible threshold
`h` and every generator `G` eventually valid on `X`, some `L ∈ X` has `β_{G,h}(L) ≤ β_h(L) - c`.

**Formalization Note.** The ambient universe is `ℤ^d` (points `Fin d → ℤ`), as in Definition 1.4
(`A, B ⊆ ℤ^d`); "languages in `ℕ^d`" is the clause that every point of every language of `X` has
nonnegative coordinates. Generators may output anywhere in `ℤ^d`. "Eventually valid on `X`" includes the global freshness convention (p.13, p.51). The
family is chosen before `h` and `G`. -/
theorem theorem_6_1 (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Fin d → ℤ)), X.Countable ∧ (∀ L ∈ X, L.Infinite) ∧
      (∀ L ∈ X, ∀ p ∈ L, ∀ i, 0 ≤ p i) ∧
      ∀ h : ℕ → ℝ, IsAdmissible h → ∀ G : GeneratorP (Fin d → ℤ), IsFreshP X G →
        IsEventuallyValidP X G → ∃ L ∈ X, betaG h G L ≤ betaH h X L - 1 / 16 := by sorry

end LocalBreadth.Supplement
