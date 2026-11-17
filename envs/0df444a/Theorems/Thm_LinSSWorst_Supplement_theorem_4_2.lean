-- Prove2me | Theorems.Thm_LinSSWorst_Supplement_theorem_4_2
-- name    : LinSSWorst.Supplement.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:48:31.35181+00:00
-- url     : https://prove2.me/theorems/a7c7dfd0-6e78-4255-9041-c6c02aaa4856
-- title:
--   Theorem 4.2 (A linear scheme for partitioned upslices) — Construction 4.1 realizes $f_\Pi$ with total share length $\le(k-t)\binom{n-q}{k-t}+qm+q\sum_{j=t}^q\binom qj$
-- statement:
--   Let $F$ be a finite field, $1\le k\le n$, $[n]=L\sqcup R$ a partition with $|R|=q$, and $t$ an integer with $1\le t\le\min(k,q)$ and $1\le k-t\le n-q$. Let $f_\Pi$ be a partitioned upslice with profile $(k-t,t)$. Set $m=\lceil\log_{|F|}(q+1)\rceil$, let $K$ be a degree-$m$ extension of $F$ (with an $F$-basis) and $\alpha_j\in K$ ($j\in R$) distinct nonzero evaluation points. Then Construction 4.1 is a linear secret-sharing scheme over $F$ realizing $f_\Pi$, and its total share length is at most
--   $$(k-t)\binom{n-q}{k-t}+qm+q\sum_{j=t}^{q}\binom qj$$
--   elements of $F$.
--
--   Covering an upslice by partitioned upslices turns this into the upslice bound of Theorem 5.3.
--
--   **Formalization Note** $R$ is the complement of $L$; "realizing" is correctness and privacy (Definition A.2) of the $F$-linear map; the total share length is the sum over parties of the sizes of their share index types. $m$ is `Nat.clog |F| (q+1)`.
--
--   Differences from the source:
--   - generalization: Shamir over the degree-m extension field K of F (one choice of K, representation and evaluation points) → every field K with Algebra F K and an F-basis indexed by Fin m, and every α injective and nonzero on R; reason: the paper fixes an arbitrary such choice; one exists (GaloisField of degree m has |F|^m − 1 ≥ q nonzero elements), so the statement specializes to the paper's
--   - encoding: F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n} → F-linear map on finite index types (traces, masking sets, Shamir coordinates, additive randomness); reason: numbering the index types gives Definition A.3's spaces
--   - encoding: m = ⌈log_{|F|}(q + 1)⌉ → m = Nat.clog (card F) (q + 1); reason: the least m with |F|^m ≥ q + 1
--   - encoding: additive sharing among the parties of U, last party P_q → the last party is the largest index of U; reason: Definition A.5 fixes some ordering of U
--   - encoding: a partition Π : [n] = L ⊔ R with |R| = q → L : Finset (Fin n), R := Lᶜ, hypothesis Lᶜ.card = q; reason: every partition is determined by L
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 4.2, p.14; standing assumptions of §4, p.13

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_construction31
import Definitions.Def_LinSSWorst_Supplement_IsUpslice
import Definitions.Def_LinSSWorst_Supplement_construction41

namespace LinSSWorst.Supplement

/-- **Theorem 4.2 (A linear scheme for partitioned upslices)**, p.14, from O. Nir, *Resolving the
Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027 submission, version of 2026-11-02,
sha256 5521cfdb…). Under the standing assumptions of §4 (p.13): a finite field `F`, integers
`1 ≤ k ≤ n`, a partition `[n] = L ⊔ R` with `|R| = q`, and `t` with `1 ≤ t ≤ min(k, q)` and
`1 ≤ k − t ≤ n − q`. For every partitioned upslice `f_Π` with profile `(k − t, t)`, Construction 4.1 is a
linear secret-sharing scheme over `F` realizing `f_Π`, and, with `m = ⌈log_{|F|}(q + 1)⌉`, its total share
length is at most `(k − t) binom(n − q, k − t) + q m + q Σ_{j=t}^{q} binom(q, j)` elements of `F`.

**Formalization Note.** `R = Lᶜ`. Linearity holds by the type of `construction41`. Definition A.4's
Shamir scheme is run over a field extension `K` of `F` given with an `F`-basis indexed by `Fin m`, where
`m = Nat.clog |F| (q + 1)` (the least `m` with `|F|^m ≥ q + 1`, i.e. `⌈log_{|F|}(q + 1)⌉`), so `K` is a
degree-`m` extension; the evaluation points `α j` of the parties `j ∈ R` are distinct and nonzero. The
statement holds for every such choice of `K`, basis and points (the paper fixes one; such choices exist).
The number of field elements held by party `i` is the cardinality of its share index type; the total share
length is their sum. `n − q` and `k − t` are exact subtractions under the hypotheses. -/
theorem theorem_4_2 {F : Type*} [Field F] [Fintype F] {n : ℕ} (k t q : ℕ) (L : Finset (Fin n))
    (hq : Lᶜ.card = q) (hk1 : 1 ≤ k) (hkn : k ≤ n) (ht1 : 1 ≤ t) (htk : t ≤ k) (htq : t ≤ q)
    (hkt1 : 1 ≤ k - t) (hktn : k - t ≤ n - q)
    (fP : (Fin n → Bool) → Bool) (hfP : IsPartitionedUpslice fP L k t)
    {K : Type*} [Field K] [Algebra F K] {m : ℕ} (hm : m = Nat.clog (Fintype.card F) (q + 1))
    (b : Module.Basis (Fin m) F K) (α : Fin n → K) (hα : Set.InjOn α (↑Lᶜ : Set (Fin n)))
    (hα0 : ∀ j ∉ L, α j ≠ 0) :
    Realizes fP (construction41 F fP L k t b α) ∧
      ∑ i, Fintype.card (ShareIdx41 L k t m i) ≤
        (k - t) * (n - q).choose (k - t) + q * m + q * ∑ j ∈ Finset.Icc t q, q.choose j := by sorry

end LinSSWorst.Supplement
