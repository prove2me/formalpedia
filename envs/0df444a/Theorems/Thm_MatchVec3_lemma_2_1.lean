-- Prove2me | Theorems.Thm_MatchVec3_lemma_2_1
-- name    : MatchVec3.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:42:33.775839+00:00
-- url     : https://prove2.me/theorems/8f2166f6-20c6-4de1-bd9c-48b7016151f0
-- title:
--   Lemma 2.1: prime-power bound $(2emn)^{m-1}$ (corrected: $n\ge1$)
-- statement:
--   Let $m=p^a$ be a prime power. For $n\ge1$, every matching vector family over $\mathbb Z^n_m$ has size at most
--
--   $$(2emn)^{m-1}.$$
--
--   In particular, for fixed $m$ there is an exponent $c$ with $MV(m,n,3)\le n^{c}$ for all $n\ge1$.
--
--   The final calculation of the paper uses this lemma to dispose of prime-power moduli.
--
--   **Formalization Note** $e$ is `Real.exp 1`. The exponent $c$ comes after $m$ and before $n$.
--
--   Differences from the source:
--   - correction: every matching vector family over Z^n_m, with no restriction on n → n ≥ 1 in both clauses; reason: at n = 0 the display is 0 for m ≥ 2, and K = 1 with empty vectors is a family; likewise MV(m, 0, 3) ≥ 1 while 0^c = 0 for c ≥ 1
--   - encoding: n^{O_m(1)} → ∃ c : ℕ, after m and before n; reason: the meaning of O_m(1)
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.1, p.9

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_MV

namespace MatchVec3

/-- **Lemma 2.1 (Prime-power bound)** (Aggarwal, Obremski, STOC 2027 submission (manuscript sha256
44199413…), Lemma 2.1, p.9): for a prime power `m`, every matching vector family over `Z_m^n` has size
at most `(2emn)^(m-1)`, and for fixed `m`, `MV(m, n, 3) ≤ n^(O_m(1))`.

**Formalization Note** The display is stated for `n ≥ 1`: at `n = 0` it reads `K ≤ 0`, while `K = 1`
with empty vectors is a family. The "in particular" clause is stated for `n ≥ 1` as well: at `n = 0`, `MV = 1` while `0 ^ c = 0` for
`c ≥ 1`. Its exponent `c` comes after `m` and before `n`. -/
theorem lemma_2_1 {m : ℕ} (hm : IsPrimePow m) :
    (∀ (n K : ℕ) (U V : Fin K → Fin n → ZMod m), 1 ≤ n → IsMVFamily U V →
      (K : ℝ) ≤ (2 * Real.exp 1 * m * n) ^ (m - 1)) ∧
    ∃ c : ℕ, ∀ n : ℕ, 1 ≤ n → MV m n 3 ≤ n ^ c := by sorry

end MatchVec3
