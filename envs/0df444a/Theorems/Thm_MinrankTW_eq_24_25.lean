-- Prove2me | Theorems.Thm_MinrankTW_eq_24_25
-- name    : MinrankTW.eq_24_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:33:14.062273+00:00
-- url     : https://prove2.me/theorems/eef9aced-09bb-4b7c-92b8-9a82b1a315ad
-- title:
--   Eqs. (24)–(25) — $\sum_{D,L}q^{\dim D\dim L}=N_q(a+c)$ and the subspace tables have size $O_q(N_q(a+c))$
-- statement:
--   Let $b=a+c$ and $s=\min\{a,c\}$. Over $\mathbb F_q$:
--
--   1. (24) $\displaystyle\sum_{D\le\mathbb F_q^a,\ L\le\mathbb F_q^{1\times c}} q^{\dim D\,\dim L}=N_q(a+c)$;
--   2. (25) there is a constant $C$ depending only on $q$ with $\displaystyle\sum_{j=0}^{s}\left[{s\atop j}\right]_q N_q(b-j)\le C\,N_q(b)$ for all $a,c$;
--   3. if $a\ge c$, the tables for $C$ have total size $\sum_{K\le\mathbb F_q^c}N_q(b-\dim K)$, which equals the sum in (25);
--   4. if $a<c$, the tables for $B$ have total size $\sum_{D\le\mathbb F_q^a}N_q(c+\dim D)$, which equals the sum in (25).
--
--   These are the counting facts behind the cost bound of Proposition 1.
--
--   Differences from the source:
--   - encoding: O_q(N_q(b)) → ≤ C·N_q(b) with C chosen after F and before a, c; reason: definition of O with a constant depending only on q
-- source:
--   Perles–Weinstein, Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs, STOC 2027 submission (manuscript sha256 32a91384…), proof of Proposition 1, p.15, Eqs. (24)–(25)

import Mathlib
import Definitions.Def_MinrankTW_Nq
import Definitions.Def_MinrankTW_gaussCount

namespace MinrankTW

/-- **Eqs. (24)–(25)** (proof of Proposition 1), Perles–Weinstein, *Efficient Algorithms for Minrank and Index Coding for Low-Treewidth Graphs*, STOC 2027 submission manuscript (sha256 32a91384…c57991), p.15. With `b = a + c` and
`s = min{a, c}`:
1. `∑_{D ≤ F^a, L ≤ F^{1×c}} q^{dim D · dim L} = N_q(a + c)` (24);
2. `∑_{j=0}^{s} [s j]_q N_q(b − j) = O_q(N_q(b))` (25), the constant depending only on `q`;
3. if `a ≥ c`, the tables for `C` have total size `∑_{K ≤ F^c} N_q(b − dim K)`, which equals the
   sum in (25);
4. if `a < c`, the tables for `B` have total size `∑_{D ≤ F^a} N_q(c + dim D)`, which equals the
   sum in (25).

**Formalization Note** Sums over subspaces are `finsum`s over the finitely many submodules;
row vectors `F^{1×c}` are `Fin c → F`. -/
theorem eq_24_25 (F : Type) [Field F] [Fintype F] :
    (∀ a c : ℕ, ∑ᶠ (D : Submodule F (Fin a → F)) (L : Submodule F (Fin c → F)),
      Fintype.card F ^ (Module.finrank F D * Module.finrank F L) = Nq F (a + c)) ∧
    (∃ C : ℕ, ∀ a c : ℕ,
      ∑ j ∈ Finset.range (min a c + 1), gaussCount F (min a c) j * Nq F (a + c - j) ≤
        C * Nq F (a + c)) ∧
    (∀ a c : ℕ, c ≤ a →
      ∑ᶠ (K : Submodule F (Fin c → F)), Nq F (a + c - Module.finrank F K) =
        ∑ j ∈ Finset.range (min a c + 1), gaussCount F (min a c) j * Nq F (a + c - j)) ∧
    (∀ a c : ℕ, a < c →
      ∑ᶠ (D : Submodule F (Fin a → F)), Nq F (c + Module.finrank F D) =
        ∑ j ∈ Finset.range (min a c + 1), gaussCount F (min a c) j * Nq F (a + c - j)) := by sorry

end MinrankTW
