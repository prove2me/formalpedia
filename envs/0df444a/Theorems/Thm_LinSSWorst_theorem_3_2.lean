-- Prove2me | Theorems.Thm_LinSSWorst_theorem_3_2
-- name    : LinSSWorst.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T04:06:36.967552+00:00
-- url     : https://prove2.me/theorems/fb779833-11a3-4b75-ac90-fbb856fbe99a
-- title:
--   Theorem 3.2 (The general linear scheme), first sentence — Construction 3.1 realizes $f$ with $2^{\ell-1}$ elements per party of $L$ and $2^{q-1}+1$ per party of $R$
-- statement:
--   Let $F$ be a finite field, $f$ an $n$-party access structure, and $[n]=L\sqcup R$ a partition into nonempty sets with $|L|=\ell$ and $|R|=q$. Then Construction 3.1 is a linear secret-sharing scheme over $F$ that realizes $f$, and
--   1. every party of $L$ holds exactly $2^{\ell-1}$ elements of $F$;
--   2. every party of $R$ holds exactly $2^{q-1}+1$ elements of $F$.
--
--   Taking $|R|=\lceil n/2\rceil$ turns this into the main theorem's bound $2^{\lceil n/2\rceil-1}+1$ for $n\ge 2$. The theorem's second sentence ("Consequently, …") is stated, for every $n$, by the goal `LinSSWorst.theorem_1_1`.
--
--   **Formalization Note** $R$ is `Lᶜ`. Linearity is part of the type of `construction31 F f L`. The number of field elements of party `i` is the cardinality of its index type `ShareIdx L i`. The subtractions are exact since $L$ and $R$ are nonempty.
--
--   Differences from the source:
--   - encoding: the partition [n] = L ⊔ R → `L : Finset (Fin n)` with R = Lᶜ, both nonempty; reason: same partitions
--   - encoding: Construction 3.1 as a map F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n} → an F-linear map on the finite index types `RandIdx L`, `ShareIdx L i`, the last party of each additive sharing being the largest index of U; reason: numbering the index types gives Definition A.3's form; the page leaves the order of the parties of U free
--   - encoding: "every party of L holds 2^{ℓ−1} elements of F" → `Fintype.card (ShareIdx L i) = 2 ^ (L.card - 1)` for i ∈ L, and 2 ^ (Lᶜ.card - 1) + 1 for i ∉ L; reason: the number of coordinates of the party's share
--   - encoding: {0,1}ⁿ; "identical distributions over uniform r" → `Fin n → Bool`; equal push-forwards of `PMF.uniformOfFintype`; reason: same objects
-- source:
--   Nir, Resolving the Worst-Case Complexity of Linear Secret Sharing, preprint (STOC 2027 submission, version of 2026-11-02, sha256 5521cfdb…), Theorem 3.2, first sentence, p.12

import Mathlib
import Definitions.Def_LinSSWorst_Realizes
import Definitions.Def_LinSSWorst_construction31

namespace LinSSWorst

/-- **Theorem 3.2 (The general linear scheme), first sentence**, p.12, from O. Nir, *Resolving the Worst-Case Complexity of Linear Secret Sharing*, preprint (STOC 2027
submission, version of 2026-11-02, sha256 5521cfdb…).
For every finite field `F`, every access structure `f` over `[n]` and every partition
`[n] = L ⊔ R` into nonempty sets with `|L| = ℓ` and `|R| = q`, Construction 3.1 is a linear
secret-sharing scheme over `F` for `f`, in which every party of `L` holds `2^{ℓ-1}` elements of
`F` and every party of `R` holds `2^{q-1} + 1` elements of `F`.

**Formalization Note.** `R = Lᶜ`. Linearity holds by the type: `construction31 F f L` is an
`F`-linear map from secret-and-randomness to the shares. "For `f`" is `Realizes` (correctness and
privacy of Definition A.2). The number of field elements held by party `i` is the cardinality of
its share index type `ShareIdx L i`; numbering the finite index types gives Definition A.3's
`F^{1+ℓ_r} → F^{ℓ_1+⋯+ℓ_n}`. The subtractions `ℓ - 1`, `q - 1` are exact since `L`, `R` are
nonempty. -/
theorem theorem_3_2 {F : Type*} [Field F] [Fintype F] {n : ℕ}
    (f : (Fin n → Bool) → Bool) (hf : IsAccessStructure f) (L : Finset (Fin n))
    (hL : L.Nonempty) (hR : Lᶜ.Nonempty) :
    Realizes f (construction31 F f L) ∧
    (∀ i ∈ L, Fintype.card (ShareIdx L i) = 2 ^ (L.card - 1)) ∧
    (∀ i ∉ L, Fintype.card (ShareIdx L i) = 2 ^ (Lᶜ.card - 1) + 1) := by sorry

end LinSSWorst
