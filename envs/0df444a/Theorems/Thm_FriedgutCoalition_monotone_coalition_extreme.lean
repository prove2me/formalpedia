-- Prove2me | Theorems.Thm_FriedgutCoalition_monotone_coalition_extreme
-- name    : FriedgutCoalition.monotone_coalition_extreme
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:27.087828+00:00
-- url     : https://prove2.me/theorems/56279fdc-cd23-4c47-8f6e-5be22fb4a4e4
-- title:
--   §2.1 — a monotone coalition forces $b$ by setting its coordinates to the extreme value
-- statement:
--   Let $f$ be monotone, $S\subseteq[n]$ a coalition and $x$ an input.
--
--   1. On $[r]^n$ ($r\ge1$): some assignment of the coordinates in $S$ gives output $1$ if and only if setting them all to $r$ does, and some assignment gives $0$ if and only if setting them all to $1$ does.
--   2. On $[0,1]^n$: the same, with the values $1$ and $0$ of $[0,1]$.
--   3. On $[0,1]^n$: the sets $\{x: f(1_S,x_{-S})=1\}$ and $\{x: f(0_S,x_{-S})=0\}$ are Lebesgue measurable, and
--
--   $$\mathbf P^1_S(f)=\lambda\{x: f(1_S,x_{-S})=1\},\qquad \mathbf P^0_S(f)=\lambda\{x: f(0_S,x_{-S})=0\}.$$
--
--   This is why $\mathbf P^b_S$ is well defined for monotone $f$ on the solid cube, and it is the identity used in the proofs of Theorem 3.1 (p.9) and Claim 4.6 (p.14).
--
--   Differences from the source:
--   - generalization: the sentence is about monotone f : [0,1]ⁿ → {0,1} → also states the equivalence on [r]ⁿ for every r ≥ 1; reason: the proofs on p.9 and p.14 use the same fact on [r]ⁿ; part 2 and 3 are the source's statement on [0,1]ⁿ
--   - reading: "the coalition can force output b precisely when setting every coordinate in S to b gives output b"; "the resulting restricted function is … Lebesgue measurable" → a pointwise iff for every x; NullMeasurableSet for the uniform measure, and cubeCoalProb equal to the measure of that set; reason: "setting to b" means the largest value for b = 1 and the least for b = 0; "Lebesgue measurable" is null measurability for the completed measure
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), §2.1, p.5 (used on pp.9, 14)

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_cubeCoalProb

namespace FriedgutCoalition

open MeasureTheory

/-- **§2.1, p.5: a monotone coalition forces `b` by setting its coordinates to the extreme value**
(Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…)). "When `f` is monotone, the coalition can force output `b`
precisely when setting every coordinate in `S` to `b` gives output `b`. The resulting restricted
function is monotone and hence Lebesgue measurable."

1. On `[r]ⁿ` (`r ≥ 1`): for every `x`, some assignment of `S` gives `1` iff assigning the largest
   value `r` (`⊤ : Fin r`) does, and some assignment gives `0` iff assigning the least value `1`
   (`0 : Fin r`) does.
2. On `[0,1]ⁿ`: the same with the values `1` and `0` of `[0,1]`.
3. On `[0,1]ⁿ`: the sets `{x | f(1_S, x_{−S}) = 1}` and `{x | f(0_S, x_{−S}) = 0}` are Lebesgue
   measurable (`NullMeasurableSet`), and `P¹_S(f)`, `P⁰_S(f)` are their measures.

**Formalization Note.** `[r]` is `Fin r`, whose least element `0` is the paper's `1` and whose top `⊤`
is the paper's `r`. Overwriting the coordinates in `S` is `S.piecewise`. -/
theorem monotone_coalition_extreme :
    (∀ (n r : ℕ) [NeZero r] (f : (Fin n → Fin r) → Bool), Monotone f →
      ∀ (S : Finset (Fin n)) (x : Fin n → Fin r),
        ((∃ j : Fin n → Fin r, f (S.piecewise j x) = true) ↔
            f (S.piecewise (fun _ => ⊤) x) = true) ∧
        ((∃ j : Fin n → Fin r, f (S.piecewise j x) = false) ↔
            f (S.piecewise (fun _ => 0) x) = false)) ∧
    (∀ (n : ℕ) (f : (Fin n → unitInterval) → Bool), Monotone f →
      ∀ (S : Finset (Fin n)) (x : Fin n → unitInterval),
        ((∃ j : Fin n → unitInterval, f (S.piecewise j x) = true) ↔
            f (S.piecewise (fun _ => 1) x) = true) ∧
        ((∃ j : Fin n → unitInterval, f (S.piecewise j x) = false) ↔
            f (S.piecewise (fun _ => 0) x) = false)) ∧
    (∀ (n : ℕ) (f : (Fin n → unitInterval) → Bool), Monotone f → ∀ S : Finset (Fin n),
      NullMeasurableSet {x : Fin n → unitInterval | f (S.piecewise (fun _ => 1) x) = true} ∧
      cubeCoalProb f S true =
        (volume {x : Fin n → unitInterval | f (S.piecewise (fun _ => 1) x) = true}).toReal ∧
      NullMeasurableSet {x : Fin n → unitInterval | f (S.piecewise (fun _ => 0) x) = false} ∧
      cubeCoalProb f S false =
        (volume {x : Fin n → unitInterval | f (S.piecewise (fun _ => 0) x) = false}).toReal) := by sorry

end FriedgutCoalition
