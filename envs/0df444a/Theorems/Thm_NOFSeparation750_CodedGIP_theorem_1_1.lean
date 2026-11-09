-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_1_1
-- name    : NOFSeparation750.CodedGIP.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:42:12.405303+00:00
-- url     : https://prove2.me/theorems/4dff664b-31cc-4786-88b7-91de439cb698
-- title:
--   Theorem 1.1 — explicit constant randomized versus linear nondeterministic separation
-- statement:
--   For every fixed integer $k\ge3$, there is one total Boolean family $F_n:(\{0,1\}^{n})^k\to\{0,1\}$, computed at every input length by one deterministic finite program in polynomial time, and constants $C\in\mathbb N$, $c>0$, and $n_0$ depending only on $k$, such that for every $n\ge n_0$,
--   $$R_k(F_n)\le C,\qquad N_k(F_n)\ge c n.$$
--   The randomized upper witness accepts every one-input with probability one and every zero-input with probability at most $1/3$. The nondeterministic lower bound applies to every correct certificate protocol, charging its certificate and verification communication.
--
--   The evaluator, randomized witnesses, and universal lower bounds all concern the same family. It is defined at every length, including zero and all lengths below the threshold. This states the full separation and the polynomial-time explicitness asserted immediately after Theorem 1.1; it does not assume an evaluator or hard codes as a premise. The padded coded-GIP construction is available as a witness through the definition layer.
--
--   Differences from the source:
--   - encoding: minimum communication complexity → existential bounded public-coin witnesses and universal bounds on correct certificate protocols; reason: these are the defining upper and lower inequalities, without a totalized minimum over admissible protocols
--   - encoding: deterministic polynomial-time algorithms → finite binary stack programs, actual halting executions, and one polynomial bound; reason: finite control and finite alphabets give the standard polynomial-time model; unary size headers have polynomial overhead
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 1.1 and immediately following explicitness paragraph, p.3; canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Programs
import Definitions.Def_NOFSeparation750_CodedGIP_Protocols

namespace NOFSeparation750.CodedGIP

/-- Theorem 1.1, p.3, including the one-sided paragraph and the immediately
following polynomial-time explicitness assertion. The same total family occurs
in the evaluator, upper witnesses, and all nondeterministic lower bounds. -/
theorem theorem_1_1 (k : ℕ) (hk : 3 ≤ k) :
    ∃ F : BooleanFamily k, UniformPolyTime F ∧
      ∃ C : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n, n₀ ≤ n →
        (∃ P : PublicProtocol (fun _ : Fin k => Bits n),
          P.Bounded C ∧ P.OneSided (F n) (1 / 3)) ∧
        (∀ P : NondetProtocol (fun _ : Fin k => Bits n), ∀ d : ℕ,
          P.Correct (F n) → P.Bounded d → c * (n : ℝ) ≤ d) := by sorry

end NOFSeparation750.CodedGIP
