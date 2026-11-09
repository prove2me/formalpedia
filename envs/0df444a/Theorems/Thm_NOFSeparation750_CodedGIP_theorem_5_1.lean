-- Prove2me | Theorems.Thm_NOFSeparation750_CodedGIP_theorem_5_1
-- name    : NOFSeparation750.CodedGIP.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T02:43:39.925347+00:00
-- url     : https://prove2.me/theorems/737d9706-895e-485e-9832-781ae5989647
-- title:
--   Theorem 5.1 — linear nondeterministic lower bound for native coded GIP
-- statement:
--   For each fixed $k\ge2$, there are constants $c>0$ and $j_0$ such that the following holds uniformly over all Section 3 field parameters and all compatible code families. Set $q=4^a$, $s=2^a$, $b=2a$, $r_j=(q-s)s^j$, and $\ell=2^{k+2}k$. Suppose every pair $V_j,W_j$ is $(6/s,3/4)$-compatible. Let $n_j=(\ell\dim V_j+\dim W_j)b$. For every $j\ge j_0$ and every correct nondeterministic NOF verifier with cost at most $d$,
--   $$d\ge c\,n_j.$$
--   Constants are chosen before the field, code family, level, and competing verifier. In particular this gives $N_k(\operatorname{CodedGIP})=\Omega_k(n_j)$ for the selected native family. This is the native-length theorem; all-length padding belongs to the main separation theorem.
--
--   Differences from the source:
--   - generalization: the selected Garcia–Stichtenoth code family of Section 3 → all (6/s,3/4)-compatible families at all allowed q, with constants chosen before these families; reason: the measure and cylinder estimates use only compatibility and the dimension upper bound from Singleton; the selected effective family is included
--   - encoding: q a power of four, r_j=(q−√q)q^(j/2), and a fixed binary field representation → q=4^a with a≥1, s=2^a, b=2a, r_j=(4^a−2^a)(2^a)^j, and a b-bit-to-field bijection; reason: this parametrizes every allowed q exactly and avoids truncated fractional natural powers; any field of that cardinality is isomorphic to the source field
--   - encoding: minimum communication complexity → universal bounds on every correct operational certificate protocol; reason: these are the defining upper and lower inequalities, without a totalized minimum over admissible protocols
--   - encoding: indices [r] and Boolean values {0,1} → zero-based Fin indices and Bool; reason: order-preserving relabeling changes no inputs, cylinders, or communication costs
-- source:
--   Haoyu Wang, Yimeng Wang, Pei Wu, STOC 2027 submission #750 (October 2026), Theorem 5.1, p.8; §3, p.7; proof p.10, equations (5.1), (5.2); canonical PDF SHA-256 b28ac89d573094bcafec49dc3a1eeadc9e95b5c3074c478d242f60a2818a42ce

import Mathlib
import Definitions.Def_NOFSeparation750_CodedGIP_Model

namespace NOFSeparation750.CodedGIP

/-- Theorem 5.1, p.8. The constants precede the field, code family, level and every
competing certificate protocol. It applies uniformly to every compatible family
with §3's parameters, including the effectively constructed pair. -/
theorem theorem_5_1 (k : ℕ) (hk : 2 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ j₀ : ℕ, ∀ a : ℕ, Allowed k a →
      ∀ (F : Type) [Field F] [Fintype F], ∀ D : PairFamily F a,
      ∀ codec : (Fin (2 * a) → Bool) ≃ F,
      (∀ j, Compatible (D j).small.code (D j).large.code k
        (6 / (2 ^ a : ℝ)) (3 / 4)) →
      ∀ j, j₀ ≤ j →
      ∀ P : NondetProtocol (fun _ : Fin k => Bits (nativeLength (D j) (copies k) (2 * a))),
      ∀ d : ℕ, P.Correct (nativeFunction (D j) codec (copies k) k) → P.Bounded d →
        c * (nativeLength (D j) (copies k) (2 * a) : ℝ) ≤ d := by sorry

end NOFSeparation750.CodedGIP
