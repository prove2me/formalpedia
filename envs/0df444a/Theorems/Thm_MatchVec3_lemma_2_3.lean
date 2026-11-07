-- Prove2me | Theorems.Thm_MatchVec3_lemma_2_3
-- name    : MatchVec3.lemma_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:41:49.787696+00:00
-- url     : https://prove2.me/theorems/4578d4f5-df3f-484c-8091-33077c61ed77
-- title:
--   Lemma 2.3: minimal modulus for 3-restricted families
-- statement:
--   Let $K\ge2$ and let $(U,V)$ be a 3-restricted matching vector family modulo $m$. Suppose that for no proper divisor $d$ of $m$ the same lists, read modulo $d$, remain a matching vector family. Then either $m$ is a prime power, or $m=p^aq^b$ for primes $p<q$ and integers $a,b\ge1$, and residues $\alpha,\beta$ exist with all off-diagonal inner products in $\{\alpha,\beta\}$ and
--
--   $$\alpha\equiv0\ (\mathrm{mod}\ p^aq^{b-1}),\quad\alpha\not\equiv0\ (\mathrm{mod}\ q^b),\qquad\beta\equiv0\ (\mathrm{mod}\ p^{a-1}q^b),\quad\beta\not\equiv0\ (\mathrm{mod}\ p^a).$$
--
--   The lemma reduces the main theorem to prime-power moduli and to this two-residue structure.
--
--   Differences from the source:
--   - encoding: "with off-diagonal residues α, β" → 2 ≤ K, with α, β existentially quantified after m and every off-diagonal value in {α, β}; reason: the phrase presupposes an off-diagonal pair, and at K ≤ 1 the minimal divisor is 1; the ∃ is the page's "after possibly interchanging α and β"
--   - generalization: "m is minimal among divisors of the original modulus" → no proper divisor of m keeps the lists a family; reason: only divisors of m are tested, so any m minimal in the page's sense satisfies it
--   - encoding: a modulus m → m ≠ 0; reason: ZMod 0 is ℤ, which is not a modulus
-- source:
--   Aggarwal, Obremski, Subexponential Upper Bounds for 3-Restricted Matching Vector Families, STOC 2027 submission (manuscript sha256 44199413…), Lemma 2.3, p.9

import Mathlib
import Definitions.Def_MatchVec3_IsMVFamily
import Definitions.Def_MatchVec3_IsRestricted
import Definitions.Def_MatchVec3_reduceList
import Definitions.Def_MatchVec3_ResidueStructure
import Definitions.Def_MatchVec3_OffDiagIn

namespace MatchVec3

/-- **Lemma 2.3 (Minimal modulus for 3-restricted families)** (Aggarwal, Obremski, STOC 2027 submission
(manuscript sha256 44199413…), Lemma 2.3, p.9): let `(U, V)` be a 3-restricted matching vector family
modulo `m` such that for no proper divisor of `m` the same lists remain a matching vector family. Then
`m` is a prime power, or `m = p^a q^b` for primes `p < q` and positive integers `a, b`, and after
possibly interchanging `α` and `β` the off-diagonal residues satisfy the four congruences of
`ResidueStructure`.

**Formalization Note** `2 ≤ K` encodes "with off-diagonal residues α, β", which presupposes an
off-diagonal pair: at `K ≤ 1` the minimal divisor is `1`. Minimality is among the divisors of `m`,
which are divisors of the original modulus; only proper divisors of `m` are tested, so any family that
is minimal in the page's sense qualifies. The conclusion places every off-diagonal value in `{α, β}`.
`m ≠ 0` says that `m` is a modulus. -/
theorem lemma_2_3 {m n K : ℕ} (hm : m ≠ 0) (hK : 2 ≤ K) (U V : Fin K → Fin n → ZMod m)
    (hfam : IsMVFamily U V) (hres : IsRestricted 3 U V)
    (hmin : ∀ d (hd : d ∣ m), d ≠ m → ¬ IsMVFamily (reduceList hd U) (reduceList hd V)) :
    IsPrimePow m ∨
      ∃ (p q a b : ℕ) (α β : ZMod m), ResidueStructure m p q a b α β ∧ OffDiagIn U V α β := by sorry

end MatchVec3
