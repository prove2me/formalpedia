-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_8_2
-- name    : LocalBreadth.Supplement.theorem_8_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:27:33.222992+00:00
-- url     : https://prove2.me/theorems/a5d35436-8137-4566-afa5-26c5ddf6ff74
-- title:
--   Theorem 8.2 — finite-rank near-half guarantee at threshold $\log^{1+\tau}(2+V)$
-- statement:
--   Fix $d\ge2$, $\tau>0$ and $0<\varepsilon<1/2$, and let $\mathcal X$ be a nonempty countable family of infinite subsets of $\mathbb Z^d$. Let
--   $$h_\tau(V)=\log^{1+\tau}(2+V).$$
--   There is one (fresh) universally eventually valid generator such that every target $K\in\mathcal X$ of finite Cantor–Bendixson point rank (in the finite-evidence topology on $\mathcal X$, Definition 3.1) satisfies, on every full enumeration of $K$,
--   $$\delta_{h_\tau}(O,K)\ge\tfrac12-\varepsilon.$$
--   No common upper bound on the finite ranks is required.
--
--   This brings the threshold of the earlier finite-rank theorem arbitrarily close to logarithmic. Theorem 9.1 shows that $\varepsilon$ cannot be removed.
--
--   Differences from the source:
--   - reading: "generator" / "eventually valid generator" (the theorem names only validity) → a generator that is fresh (IsFresh…) and universally eventually valid on the family; reason: the model conventions (p.13, used in Part II by p.51) require the global freshness condition o_t ∉ S_t ∪ O_{t−1} of every generator throughout the paper
--   - encoding: log^{1+τ}(2 + V) → Real.log (2 + V) ^ (1 + τ) (real power of the natural logarithm); reason: log^{1+τ} is the (1+τ)-th power of the logarithm; log(2 + V) > 0, so the real power is the usual one
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §8, Theorem 8.2, p.70 (PDF p.72)

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_GeneratorP
import Definitions.Def_LocalBreadth_Supplement_deltaH
import Definitions.Def_LocalBreadth_Supplement_HasFiniteCBRank

namespace LocalBreadth.Supplement

/-- Theorem 8.2 (finite-rank near-half guarantee). Kleinberg, Wei, STOC 2027 submission (manuscript
sha256 f924cbfc…), §8, p.70. Fix `d ≥ 2`, `τ > 0` and `0 < ε < 1/2`, and let `X` be a nonempty countable
family of infinite subsets of `ℤ^d`. With `h_τ(V) = log^{1+τ}(2 + V)`, there is one universally
eventually valid generator such that every target `K ∈ X` of finite Cantor–Bendixson point rank
satisfies `δ_{h_τ}(O, K) ≥ 1/2 - ε` on every full enumeration of `K`. No common bound on the ranks is
required.

**Formalization Note.** `log^{1+τ}` is the `(1+τ)`-th power of the natural logarithm (`Real.rpow`).
The generator satisfies the global freshness convention (p.13, p.51) and is eventually valid on all of
`X`; the rank is taken in the finite-evidence topology on `X` (Definition 3.1). -/
theorem theorem_8_2 (d : ℕ) (hd : 2 ≤ d) (τ ε : ℝ) (hτ : 0 < τ) (hε : 0 < ε) (hε' : ε < 1 / 2)
    (X : Set (Set (Fin d → ℤ))) (hne : X.Nonempty) (hc : X.Countable)
    (hinf : ∀ L ∈ X, L.Infinite) :
    ∃ G : GeneratorP (Fin d → ℤ), IsFreshP X G ∧ IsEventuallyValidP X G ∧
      ∀ K ∈ X, HasFiniteCBRank X K → ∀ x, IsFullEnumerationP K x →
        1 / 2 - ε ≤ deltaH (fun V : ℕ => Real.log (2 + V) ^ (1 + τ)) (outputSetP G x) K := by sorry

end LocalBreadth.Supplement
