-- Prove2me | Theorems.Thm_KSATWindow_theorem_4_1
-- name    : KSATWindow.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:31:46.1592+00:00
-- url     : https://prove2.me/theorems/f6809c06-4437-4224-a376-c3f6e054f6db
-- title:
--   Theorem 4.1 (Aldous) — $\operatorname{Var}(T)\le\kappa\,\mathbb E T\,\mathbb E[c(\mathcal T)]$ for cover times
-- statement:
--   Let $X$ be a nonempty finite set, and let $Y_1,Y_2,\dots$ be independent copies of a random subset of $X$ such that $\mathbb P(x\in Y_1)>0$ for every $x\in X$. Let $T$ be the first time these sets cover $X$, and let $\mathcal T=X\setminus\bigcup_{i<T}Y_i$ be the last uncovered set. For a deterministic $A\subseteq X$, let $c(A)$ be the expected time to cover $A$ using a fresh independent sequence with the same law. There is an absolute constant $\kappa$ such that
--   $$\operatorname{Var}(T)\le\kappa\,\mathbb E T\;\mathbb E[c(\mathcal T)].$$
--
--   A cover time is concentrated when its last uncovered set is quickly covered by a fresh sequence. The paper cites this from Aldous (1991), Theorem 1(b), and applies it with $X=\{0,1\}^n$ and $Y_i$ the assignments falsifying the $i$-th clause.
--
--   Differences from the source:
--   - encoding: a random subset of X → its membership indicator X → Bool with an arbitrary probability law; reason: subsets and indicators correspond bijectively
--   - encoding: X a nonempty finite set → X : Type with Fintype and Nonempty; reason: every finite set is in bijection with a type in the lowest universe
--   - encoding: Var(T), E T, E[c(𝒯)] → evariance in [0,∞] and lower integrals in [0,∞]; reason: no junk value: a finite right side forces a finite variance
-- source:
--   Carenini, A polynomial scaling window for random k-SAT and a proof of the satisfiability conjecture, STOC 2027 submission (manuscript sha256 1664cf10…), §4, p.8, Theorem 4.1 (Aldous [5], Theorem 1(b))

import Mathlib
import Definitions.Def_KSATWindow_CoverTime
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace KSATWindow

/-- **Theorem 4.1, p.8 (Aldous [5], Theorem 1(b)) — variance of a cover time.** G. Carenini, *A polynomial scaling window for random k-SAT and a proof of the satisfiability
conjecture*, STOC 2027 submission (manuscript sha256 1664cf10…), §4, p.8.

Let `X` be a nonempty finite set, and let `Y₁, Y₂, …` be independent copies of a random subset of
`X` such that `P(x ∈ Y₁) > 0` for every `x ∈ X`. Let `T` be the first time these sets cover `X`,
and let `𝒯 = X ∖ ⋃_{i<T} Y_i` be the last uncovered set. For deterministic `A ⊆ X`, let `c(A)` be
the expected time to cover `A` using a fresh independent sequence with the same law. There is an
absolute constant `κ` such that `Var(T) ≤ κ · E T · E[c(𝒯)]`.

**Formalization Note.** `κ` is chosen before `X` and the law. A random subset is its membership
indicator `X → Bool` with law `ν`. `Var(T)` is `evariance` (in `[0, ∞]`, never a junk `0`);
`E T` and `E[c(𝒯)]` are lower integrals in `[0, ∞]`. `X` ranges over `Type`. -/
theorem theorem_4_1 :
    ∃ κ : NNReal, ∀ (X : Type) [Fintype X] [Nonempty X] (ν : Measure (X → Bool))
      [IsProbabilityMeasure ν], (∀ x : X, 0 < ν {Y | Y x = true}) →
        evariance (fun ω => ((coverTime ω).toNat : ℝ)) (subsetStreamLaw ν) ≤
          (κ : ℝ≥0∞) * (∫⁻ ω, ((coverTime ω : ℕ∞) : ℝ≥0∞) ∂(subsetStreamLaw ν)) *
            ∫⁻ ω, coverMean ν (lastUncovered ω) ∂(subsetStreamLaw ν) := by sorry

end KSATWindow
