-- Prove2me | Theorems.Thm_MultiplierAssoc206_Resolution_theorem_8_8
-- name    : MultiplierAssoc206.Resolution.theorem_8_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:18:46.972378+00:00
-- url     : https://prove2.me/theorems/ec09ea9f-75a1-4c34-abee-fe5761aa7eea
-- title:
--   Lower bound for multiplier associativity: $\mathrm{size}_{\mathrm{Res}}(\mathsf{Assoc}_n)\ge 2^{\Omega((n/\log n)^{1/4})}$
-- statement:
--   Let $(\mathrm{Mul}_n)_n$ be a strip-local multiplier encoding family (Definition 4.3), for instance the array multiplier or the Wallace-tree multiplier, and let $\mathsf{Assoc}_n$ be the associativity formula built from it (Definition 3.1), which asserts $(xy)z\ne x(yz)$ for $n$-bit inputs. There are $c>0$ and $N$ such that for all $n\ge N$
--   $$\mathrm{size}_{\mathrm{Res}}(\mathsf{Assoc}_n)\ \ge\ 2^{\,c\,(n/\log n)^{1/4}}.$$
--
--   This is the first resolution lower bound for a natural formula about multiplication without restrictions on the order of resolution steps, and it bounds below the running time of CDCL SAT solvers on multiplier associativity.
--
--   **Formalization Note** $\mathrm{size}_{\mathrm{Res}}$ is an infimum in $\mathbb N$, so the inequality also asserts that a refutation exists; $\mathsf{Assoc}_n$ is unsatisfiable for exact encodings and resolution is complete. The logarithm is natural; another base only changes $c$.
--
--   Differences from the source:
--   - encoding: for all sufficiently large n, size_Res(Assoc_n) ≥ 2^{Ω((n/log n)^{1/4})} → there are c > 0 and N, depending on the family, with size_Res(Assoc_n) ≥ 2^{c (n/log n)^{1/4}} for all n ≥ N (natural logarithm); reason: explicit form of the asymptotic notation; the base of the logarithm only changes c, and the threshold may be increased to at least 2 to keep log n positive
-- source:
--   Vincent Liew, Associativity of Multiplication Is Hard for Resolution, STOC 2027 submission #206 (October 2026), source.pdf SHA-256 676dcc4be9158c52d07aec1c9d48f53fa38289ed1b4dcb34b53adc70dbdd5ead, PDF p.22 (printed p.21), Theorem 8.8

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_Assoc

namespace MultiplierAssoc206.Resolution

/-- Theorem 8.8 (Lower bound for multiplier associativity), PDF p.22 (printed p.21): for every
strip-local multiplier encoding family there are `c > 0` and `N` with
`size_Res(Assoc_n) ≥ 2^(c (n / log n)^(1/4))` for all `n ≥ N`. -/
theorem theorem_8_8 (Mul : (n : ℕ) → MulEncoding n) (hMul : StripLocal Mul) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (2 : ℝ) ^ (c * ((n : ℝ) / Real.log n) ^ ((1 : ℝ) / 4)) ≤ (sizeRes (Assoc Mul n) : ℝ) := by sorry

end MultiplierAssoc206.Resolution
