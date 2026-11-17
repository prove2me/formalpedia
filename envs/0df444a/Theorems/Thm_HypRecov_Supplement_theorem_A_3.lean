-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_A_3
-- name    : HypRecov.Supplement.theorem_A_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:29:22.872551+00:00
-- url     : https://prove2.me/theorems/19d25dc0-50d1-47ab-842c-791eb9be0ff9
-- title:
--   Theorem A.3 — sparse recovery by $2K$ power syndromes
-- statement:
--   For every $n\ge r\ge1$, use one deterministic field $\mathbb F_{2^s}$ and the labels of Lemma A.2. For every $K\ge1$ and every field-valued vector $\mu$ on the $r$-subsets with at most $K$ nonzero coordinates, the $2K$ measurements
--   $$S_j=\sum_e\mu_e\alpha(e)^j,\qquad 0\le j<2K,$$
--   recover its support and all coefficients deterministically. Each measurement has Boolean-slice degree at most
--   $$d_K=\min\{r,\lfloor\log_2K\rfloor+1\}.$$
--
--   One common measurement map and decoder work for every $K$-sparse vector. Measurements, deterministic description, output and workspace use $O(Kr\log(n+1))$ bits, and encoding and decoding are polynomial in $n,r,K$. If $n\ge2r$, every lower degree has two distinct $K$-sparse field vectors that agree under every measurement of that degree.
--
--   Differences from the source:
--   - encoding: the constructible field and labels of Lemma A.2 → `GaloisField 2 s`, an injective additive label on all sets of size at most $r$, injective binary field codes, and uniform field-construction, label and set-decoding machines with explicit bounds; reason: these are exactly the interface clauses of Lemma A.2 used by Theorem A.3
--   - encoding: degree-$d$ polynomial measurement on the $r$-uniform Boolean slice → a coefficient function supported on monomials $B$ with $|B|\le d$, evaluated only on $r$-sets; reason: this is the unique multilinear representative on the Boolean cube restricted to the slice
--   - encoding: deterministic polynomial-time encoder/decoder and $O(Kr\log(n+1))$ bits → common TM2 machines with absolute constants, binary encodings, and all-stack step/space bounds; reason: explicit resource interpretation with the same instances
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem A.3, pp.30-31 (PDF pp.31-32); Lemma A.2, p.29 (PDF p.30)

import Mathlib
import Definitions.Def_HypRecov_Supplement_InnerSyndromeData

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem A.3 (Sparse recovery on the Boolean slice).** Zhang, Chen, Shen, *Hypergraph Recovery
from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Theorem A.3,
pp.30–31 (PDF pp.31–32).

There are one deterministic inner field/label construction and one common decoder such that the
first `2K` power syndromes recover the support and every field coefficient of every `K`-sparse
vector on the `r`-uniform Boolean slice.  The `j`-th syndrome is a slice polynomial of degree at
most `d_K=min{r,floor(log₂ K)+1}`.  Description, measurements, output and decoder workspace use
`O(Kr log(n+1))` bits and encoding/decoding are uniformly polynomial.  For `n ≥ 2r`, every lower
degree admits two distinct `K`-sparse vectors indistinguishable by every measurement of that degree.

**Formalization Note.** `InnerSyndromeData` records exactly Lemma A.2's field and label interface,
while `InnerSyndromeAlgorithms` supplies one field-construction, label, set-decoding, syndrome-
encoding and syndrome-decoding machine for all parameters.  Coefficients range over the full field,
not just zero-one values. -/
theorem theorem_A_3 :
    ∃ (A : InnerSyndromeAlgorithms) (C c : ℕ), ∀ (n r : ℕ), r ≤ n → 1 ≤ r →
      ∃ D : InnerSyndromeData n r,
        InnerSyndromeConditions A D C c ∧ ∀ K : ℕ, 1 ≤ K →
          let dK := min r (Nat.log 2 K + 1)
          PowerSyndromeGuarantee (K := K) A D C c ∧
          (∀ j : ℕ, j < 2 * K →
            SliceDegreeAtMost r dK (fun e => (alpha D e.1) ^ j)) ∧
          (∀ mu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s,
            (fieldSupport r mu).card ≤ K →
            (encPowerSyndromes (K := K) D mu).length + D.description.length ≤
              C * K * r * Nat.clog 2 (n + 1)) ∧
          (2 * r ≤ n → ∀ q : ℕ, q < dK →
            ∃ mu nu : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s,
              (fieldSupport r mu).card ≤ K ∧ (fieldSupport r nu).card ≤ K ∧ mu ≠ nu ∧
              ∀ f : {e : Finset (Fin n) // e.card = r} → GaloisField 2 D.s,
                SliceDegreeAtMost r q f → measureVector f mu = measureVector f nu)
    := by sorry

end HypRecov.Supplement
