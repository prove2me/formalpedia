-- Prove2me | Theorems.Thm_LocalBreadth_Supplement_theorem_6_2
-- name    : LocalBreadth.Supplement.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:25:21.429718+00:00
-- url     : https://prove2.me/theorems/ea97d2dd-df24-4c11-aede-25c48233be1e
-- title:
--   Theorem 6.2 — values $1/4$, $1/2$ and the trade-off $x+y\le1/2$
-- statement:
--   For every $d\ge2$ there are a single countable family $\mathcal X$ of infinite languages in $\mathbb N^d\subseteq\mathbb Z^d$ and a distinguished language $L_0\in\mathcal X$ such that, for every admissible threshold $h$:
--   1. $\beta_h(L_0)=1/4$ and $\beta_h(L)=1/2$ for every $L\in\mathcal X$, $L\ne L_0$;
--   2. one generator eventually valid on all of $\mathcal X$ guarantees $\delta_h(O,L)\ge1/2$ simultaneously for every $L\in\mathcal X\setminus\{L_0\}$;
--   3. if one eventually valid generator guarantees density $x$ at $L_0$ and density $y$ at every other language, then
--   $$x+y\le\tfrac12;$$
--   4. consequently, for no fixed $0<\varepsilon<1/8$ does an eventually valid generator guarantee $\delta_h(O,L)\ge\beta_h(L)-\varepsilon$ at every $L\in\mathcal X$.
--
--   The family and $L_0$ do not depend on $h$, so the same family witnesses the incompatibility for ordinary lower Banach density ($h\equiv1$) and for every admissible filtered threshold.
--
--   Differences from the source:
--   - reading: "generator" / "eventually valid generator" (the theorem names only validity) → a generator that is fresh (IsFresh…) and universally eventually valid on the family; reason: the model conventions (p.13, used in Part II by p.51) require the global freshness condition o_t ∉ S_t ∪ O_{t−1} of every generator throughout the paper
--   - reading: infinite languages in ℕ^d (the universe of outputs is not named in §6) → languages are Set (Fin d → ℤ) whose points all have nonnegative coordinates, and generators output points of ℤ^d; reason: Definition 1.4 takes A, B ⊆ ℤ^d, and Part II lets the generator output anywhere in ℤ^d (Lemma 9.2); ℕ^d is the subset of ℤ^d with nonnegative coordinates
--   - encoding: h : ℕ_{≥1} → (0, ∞) → h : ℕ → ℝ with positivity and monotonicity required on n ≥ 1 only; reason: δ_h evaluates h only at volumes V(R) ≥ 1, so the value h 0 is never used
--   - encoding: densities x, y (clause 3) → x y : ℝ arbitrary reals; reason: a guarantee x < 0 or y < 0 makes x + y ≤ 1/2 follow from the other guarantee and clause 1, so quantifying over all reals states the same clause
--   - encoding: time t = 1, 2, … with inputs x_t, outputs o_t → 0-indexed time; the output at time t is G applied to x 0, …, x t; reason: index shift only; the same runs
-- source:
--   Kleinberg, Wei, Characterizing Local Breadth in Language Generation, STOC 2027 submission (manuscript sha256 f924cbfc309339291b1a61b8504342f4050ece6e4e903dd18b2bf541446f1064), §6, Theorem 6.2, pp.42–43 (PDF pp.44–45)

import Mathlib
import Definitions.Def_LocalBreadth_Supplement_betaH

namespace LocalBreadth.Supplement

/-- Theorem 6.2. Kleinberg, Wei, STOC 2027 submission (manuscript sha256 f924cbfc…), §6, pp.42–43. For
every `d ≥ 2` there exist a single countable family `X` of infinite languages in `ℕ^d` and a
distinguished `L₀ ∈ X` such that, for every admissible threshold `h`:
1. `β_h(L₀) = 1/4` and `β_h(L) = 1/2` for every `L ≠ L₀`;
2. one generator eventually valid on all of `X` guarantees `δ_h(O, L) ≥ 1/2` for every `L ∈ X \ {L₀}`;
3. if one eventually valid generator guarantees density `x` at `L₀` and density `y` at every other
   language, then `x + y ≤ 1/2`;
4. consequently no eventually valid generator guarantees `δ_h(O, L) ≥ β_h(L) - ε` at every `L ∈ X`,
   for any fixed `0 < ε < 1/8`.

**Formalization Note.** The ambient universe is `ℤ^d` (points `Fin d → ℤ`), as in Definition 1.4
(`A, B ⊆ ℤ^d`); "languages in `ℕ^d`" is the clause that every point of every language of `X` has
nonnegative coordinates; generators may output anywhere in `ℤ^d`; "eventually valid" includes the global freshness convention (p.13, p.51). `X` and `L₀` are
chosen before `h`. In clause 3, `x` and `y` range over all reals. -/
theorem theorem_6_2 (d : ℕ) (hd : 2 ≤ d) :
    ∃ X : Set (Set (Fin d → ℤ)), ∃ L₀ ∈ X, X.Countable ∧ (∀ L ∈ X, L.Infinite) ∧
      (∀ L ∈ X, ∀ p ∈ L, ∀ i, 0 ≤ p i) ∧
      ∀ h : ℕ → ℝ, IsAdmissible h →
        (betaH h X L₀ = 1 / 4 ∧ ∀ L ∈ X, L ≠ L₀ → betaH h X L = 1 / 2) ∧
        (∃ G : GeneratorP (Fin d → ℤ), IsFreshP X G ∧ IsEventuallyValidP X G ∧
          ∀ L ∈ X, L ≠ L₀ → ∀ x, IsFullEnumerationP L x → 1 / 2 ≤ deltaH h (outputSetP G x) L) ∧
        (∀ G : GeneratorP (Fin d → ℤ), IsFreshP X G → IsEventuallyValidP X G → ∀ x y : ℝ,
          (∀ e, IsFullEnumerationP L₀ e → x ≤ deltaH h (outputSetP G e) L₀) →
          (∀ L ∈ X, L ≠ L₀ → ∀ e, IsFullEnumerationP L e → y ≤ deltaH h (outputSetP G e) L) →
          x + y ≤ 1 / 2) ∧
        (∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ∀ G : GeneratorP (Fin d → ℤ), IsFreshP X G →
          IsEventuallyValidP X G →
          ¬ ∀ L ∈ X, ∀ e, IsFullEnumerationP L e → betaH h X L - ε ≤ deltaH h (outputSetP G e) L) := by sorry

end LocalBreadth.Supplement
