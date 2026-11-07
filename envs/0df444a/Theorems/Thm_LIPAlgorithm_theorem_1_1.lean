-- Prove2me | Theorems.Thm_LIPAlgorithm_theorem_1_1
-- name    : LIPAlgorithm.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:40.420031+00:00
-- url     : https://prove2.me/theorems/30f654f2-e2b6-44a1-bc38-46e381f86b0c
-- title:
--   Theorem 1.1 — all isomorphisms of rank-$n$ integral lattices in $O(n\sqrt{\log n})^n$ time
-- statement:
--   There are a machine and constants $C,K$ and $c>0$ with the following property. For every $n\ge1$ and all symmetric positive definite $G_1,G_2\in\mathbb Z^{n\times n}$, with $\ell$ the length of the encoding of the instance and
--
--   $$T=\Big\lceil\big(Cn\sqrt{\log(n+2)}\big)^n(\ell+1)^K\Big\rceil,$$
--
--   the machine, on the instance followed by a string of $T$ coins, halts within $2T$ steps for every coin string, and for a fraction at least
--
--   $$1-2^{-c\,n\log n}$$
--
--   of the coin strings it outputs a duplicate-free list of exactly
--
--   $$\mathrm{Iso}(G_1,G_2)=\{U\in GL_n(\mathbb Z):G_1=U^\top G_2U\}.$$
--
--   In particular it outputs the empty list if the lattices are not isomorphic. This is the main theorem of the paper. It improves the bound $n^{O(n)}$ of Haviv and Regev, and solves the decision and search versions of the Lattice Isomorphism Problem as well.
--
--   Differences from the source:
--   - reading: a randomized algorithm, in an unnamed machine model → one Mathlib TM2 machine, with runs counted per input (Turing.TM2OutputsInTime); reason: the paper names no model; TM2 is the strongest standard reading, and the only steps above 2^{O(n)} (table, duplicate removal, cross-product filter) run on stacks with near-linear overhead, so the bound survives
--   - encoding: time O(n√log n)ⁿ up to polynomial factors in the input encoding length → ⌈(C·n·√log(n+2))ⁿ·(ℓ+1)^K⌉₊ with C, K before the instance; reason: footnote 2, p.2; log(n+2) replaces log n, which is 0 at n = 1, and for n ≥ 2 the class of bounds is unchanged
--   - reading: a randomized algorithm running in that time → halts within 2T steps on every string of exactly T coins, which are a suffix of the input; reason: the proof caps every random loop, so the worst case is what it provides; a TM2 has to pop unused coins before halting
--   - reading: outputs the full set Iso(L₁, L₂) → outputs a duplicate-free list with exactly that set of matrices; reason: the algorithm removes duplicates, and ∅ is the empty list
--   - encoding: probability at least 1 − 2^{−Ω(n log n)}, for large n → the coin fraction is at least 1 − 2^{−c·n·log n}, for all n ≥ 1, with c before the instance; reason: the bound is vacuous at n = 1, and for n < n₀ the printed algorithm is deterministic
--   - encoding: rank-n integral lattices L₁, L₂ and Iso(L₁, L₂) → integer Gram matrices G₁, G₂ and Iso(G₁, G₂); reason: the paper's own input convention, p.2 and §2.2, p.10
-- source:
--   Aggarwal, Jiang, Li, Liu, An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem, STOC 2027 submission (manuscript sha256 61ee52aa…), Theorem 1.1, p.2 (PDF p.5); Theorem 7.3, p.41 (PDF p.44)

import Mathlib
import Definitions.Def_LIPAlgorithm_encInst
import Definitions.Def_LIPAlgorithm_RunsWithin

namespace LIPAlgorithm

/-- **Theorem 1.1 (Main theorem), all isomorphisms in `O(n√log n)ⁿ` time.**
Aggarwal, Jiang, Li, Liu, *An n^{n+o(n)}-Time Algorithm for the Lattice Isomorphism Problem*, STOC 2027
submission (manuscript sha256 61ee52aa…), Theorem 1.1, p.2 (PDF p.5), restated as Theorem 7.3, p.41 (PDF p.44).

There is one machine and constants `C`, `K`, `c > 0`, chosen before the instance, such that for every `n ≥ 1` and
all integral positive definite `G₁`, `G₂`, with `ℓ` the input length and `T = ⌈(C·n·√log(n+2))ⁿ·(ℓ+1)^K⌉`:
the machine halts within `2T` steps on the input followed by any `T` coins, and for at least a fraction
`1 − 2^{−c·n·log n}` of the coins it outputs a duplicate-free list of exactly `Iso(G₁, G₂)`.

**Formalization Note.** The paper names no machine model: this is Mathlib's TM2, per input. Coins are a suffix of
the input, of length exactly `T`. The bound is `2T` because a halting TM2 must have emptied its input stack, so it
has to pop the coins it did not use. `log(n+2)` replaces `log n`, which is `0` at `n = 1`. An empty list is the
printed "outputs ∅". -/
theorem theorem_1_1 :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (C K : ℕ) (c : ℝ), 0 < c ∧
      ∀ (n : ℕ) (G₁ G₂ : Gram n), 1 ≤ n → IsGram G₁ → IsGram G₂ →
        let T := budget C K n (encInst G₁ G₂).length
        (∀ coins : List.Vector Bool T,
          ∃ out, RunsWithin M (encInst G₁ G₂ ++ coins.toList) out (2 * T)) ∧
        1 - (2 : ℝ) ^ (-(c * n * Real.log n)) ≤
          coinFraction T fun coins =>
            ∃ Us : List (Gram n), Us.Nodup ∧ (∀ U, U ∈ Us ↔ U ∈ isoSet G₁ G₂) ∧
              RunsWithin M (encInst G₁ G₂ ++ coins) (encMatList Us) (2 * T) := by sorry

end LIPAlgorithm
