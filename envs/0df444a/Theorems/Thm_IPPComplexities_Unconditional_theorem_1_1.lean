-- Prove2me | Theorems.Thm_IPPComplexities_Unconditional_theorem_1_1
-- name    : IPPComplexities.Unconditional.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:26:16.466041+00:00
-- url     : https://prove2.me/theorems/3110576b-2487-4a2d-8fe7-f13ea4112df0
-- title:
--   Theorem 1.1 — unconditional query and communication lower bound
-- statement:
--   There exist one property $L\subseteq\{0,1\}^*$, one fixed proximity $0<\varepsilon_0<1$, one deterministic finite Turing machine $M$, and one positive integer $C$ such that $M$ decides $L$ on every input and
--
--   $$\operatorname{time}_M(x)\le 2^{\,2^{C(|x|+1)}}.$$
--
--   For every nonuniform private-coin IPP family $V$ valid for $L$ at that proximity, and every pair $q,c:\mathbb N\to\mathbb N$ of worst-case bounds on its actual query count and total transmitted bits, there exist a real $\kappa>0$ and an integer $N\ge2$ such that
--
--   $$\forall n\ge N,\qquad q(n)+c(n)\ge\kappa\frac{n}{\log_2 n}.$$
--
--   The language, proximity, machine, and time constant are chosen before the verifier. The lower-bound coefficient and threshold may depend on the verifier and its resource bounds, but never on $n$. Query adaptivity, arbitrary private probability laws, arbitrary length-dependent round counts, unbounded computation, and nonrecursive strategies are included. There is no hardness assumption. A single language satisfies both the time clause and the eventual lower bound, including all sufficiently large odd and even lengths.
--
--   The result identifies a decidable property for which no such interactive system substantially improves the order of the sum of the two trivial linear-resource protocols, beyond the logarithmic factor.
--
--   **Formalization Note** The uniform decider uses Mathlib's single-tape Post-Turing semantics. A fixed positive $C$ absorbs ordinary machine simulation and finite-input overhead in the source's double-exponential time class. No numerical proximity or lower-bound coefficient is invented.
--
--   Differences from the source:
--   - generalization: IPPs valid for every positive proximity, with the proximity then fixed for lower bounds → systems required to be valid only at the single proximity under consideration; reason: every full IPP restricts to such a system; the source argument at that proximity needs no validity elsewhere
--   - encoding: unrestricted private-coin oracle interaction → arbitrary laws on finite compatible private plans, with behavioral provers seeing only the public bit transcript; reason: finite external interaction can be unfolded with private correlations retained; public framing and perfect recall preserve the source model, and the operational bridge is a proof obligation rather than an added hypothesis
--   - encoding: Boolean functions on [n], a sufficiently small constant proximity, and Ω(n/log n) → Fin n inputs corresponding to lists, one existential 0<ε₀<1, and κ>0,N≥2 before every n≥N using real base-two logarithms; reason: zero-based indexing changes no input; the empty slice and n=0 conventions are explicit; logarithm base and finite exceptional lengths are absorbed by κ and N
--   - encoding: double-exponential decidability, with 2^(2^n) displayed in the proof → one finite deterministic Post-Turing machine with the uniform bound 2^(2^(C*(n+1))) for one fixed positive C; reason: single-tape simulation has polynomial overhead, which this bound absorbs within the same double-exponential class
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), p. 1, Theorem 1.1; proof pp. 8–9; model pp. 5–7 (PDF pp. 3, 10–11, 7–9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_validity
import Definitions.Def_IPPComplexities_Unconditional_timedDecider

namespace IPPComplexities.Unconditional

/-- Theorem 1.1, both clauses: one uniformly double-exponential decidable language
and an eventual lower bound against all nonuniform private-coin systems. -/
theorem theorem_1_1 :
    ∃ (L : Property) (ε₀ : ℝ) (M : Decider) (C : ℕ),
      0 < ε₀ ∧ ε₀ < 1 ∧ 0 < C ∧
      DecidesWithin M L (fun n => 2 ^ (2 ^ (C * (n + 1)))) ∧
      ∀ (V : System) (q c : ℕ → ℕ),
        ValidAt L ε₀ V → ResourceBounds V q c →
        ∃ (κ : ℝ) (N : ℕ), 0 < κ ∧ 2 ≤ N ∧
          ∀ n : ℕ, N ≤ n →
            κ * ((n : ℝ) / Real.logb 2 (n : ℝ)) ≤ (q n + c n : ℕ) := by sorry

end IPPComplexities.Unconditional
