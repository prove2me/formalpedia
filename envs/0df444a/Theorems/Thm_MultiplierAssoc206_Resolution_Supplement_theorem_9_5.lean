-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_Supplement_theorem_9_5
-- name    : MultiplierAssoc206.Resolution.Supplement.theorem_9_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:35:55.844686+00:00
-- url     : https://prove2.me/theorems/b1c00507-2d88-4076-8cda-8fac33f885fc
-- title:
--   Theorem 9.5 — Bounded-depth Frege refutations of Assoc_n require size exp(n^(γ/d))
-- statement:
--   Fix a Frege system and let $\mathrm{Mul}_n$ be a strip-local multiplier encoding. There is a constant $\gamma>0$, depending only on the encoding (and the fixed system), and a threshold $N$ such that for all $n\ge N$ and all depths $d$ with
--   $$1\le d\le\frac{\gamma\log n}{\log\log n},$$
--   every Frege refutation $\pi$ of the associativity formula $\mathrm{Assoc}_n$ (read as a set of Frege formulas) of depth at most $d$ has size
--   $$|\pi|\ \ge\ \exp\bigl(n^{\gamma/d}\bigr),$$
--   that is, $\mathrm{size}_{\mathrm{Frege}_d}(\mathrm{Assoc}_n)\ge\exp(n^{\gamma/d})$. Logarithms are natural.
--
--   The resolution lower bound of the mission (Theorem 8.8) concerns depth-$1$ lines that are clauses; this theorem extends hardness of multiplier associativity to every bounded-depth Frege system, and to depths growing up to order $\log n/\log\log n$.
--
--   **Formalization Note** The minimum $\mathrm{size}_{\mathrm{Frege}_d}$ is replaced by a bound on every refutation of depth at most $d$, which is the same statement and avoids a minimum over a possibly empty set. Håstad's lower bound for the odd grid (Theorem 9.3) is not a hypothesis: the statement is unconditional.
--
--   Differences from the source:
--   - encoding: size_Frege_d(Assoc_n) ≥ exp(n^(γ/d)), a minimum → every refutation of depth at most d has size at least exp(n^(γ/d)); reason: the same statement without a minimum over a set that could be empty
--   - encoding: "all d ≤ γ log n / log log n" → natural numbers d with 1 ≤ d ≤ γ log n / log log n; reason: n^(γ/d) is undefined at d = 0
--   - reading: γ "depending only on the encoding" → γ is chosen after the Frege system and the encoding; reason: the Frege system is fixed throughout §9, so "only on the encoding" is said with the system fixed; the proof's γ comes from the constants of Lemma 9.4, which depend on the system
--   - reading: the size of a formula is "its number of symbols" → symbols counted in prefix form; reason: the source does not fix a notation
--   - encoding: implicational completeness for every Γ → required only for finite Γ in the definition of a Frege system; reason: equivalent by the compactness theorem, so the same systems qualify
--   - encoding: a clause as a formula → the disjunction of its literals listed in one fixed order; reason: the source does not specify an order
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.25 (printed p.24), Theorem 9.5 (Bounded-depth Frege lower bound)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Supplement_Frege
import Definitions.Def_MultiplierAssoc206_Resolution_Assoc

set_option autoImplicit false

namespace MultiplierAssoc206.Resolution.Supplement

/-- Theorem 9.5 (Bounded-depth Frege lower bound), PDF p.25 (printed p.24): for a Frege system
and a strip-local multiplier encoding there is `γ > 0` such that for all sufficiently large `n`
and all depths `1 ≤ d ≤ γ log n / log log n`, every depth-`d` Frege refutation of `Assoc_n` has
size at least `exp(n^(γ/d))`. -/
theorem theorem_9_5 (R : List Rule) (hR : IsFregeSystem R)
    (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul) :
    ∃ γ : ℝ, 0 < γ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ d : ℕ, 1 ≤ d →
      (d : ℝ) ≤ γ * Real.log n / Real.log (Real.log n) →
      ∀ π : List (Formula (AVar Mul n)),
        IsRefutation R (cnfFormulas (Assoc Mul n)) π → derivDepth π ≤ d →
          Real.exp ((n : ℝ) ^ (γ / d)) ≤ (derivSize π : ℝ) := by sorry

end MultiplierAssoc206.Resolution.Supplement
