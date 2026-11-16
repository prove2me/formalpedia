-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_4_1
-- name    : GoldProxGap.Supplement.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:46:19.702198+00:00
-- url     : https://prove2.me/theorems/07889b28-dc8c-44bd-bf25-1f57f0d20811
-- title:
--   Theorem 4.1 — quadratic count at rate $1/16$: $M=(N-1)(N-2)/6$ exceptional challenges on every binary additive domain
-- statement:
--   **Theorem 4.1 (Quadratic count at rate 1/16).** Let $\mathbb B$ be a finite field of characteristic two and $D\subseteq\mathbb B$ a binary additive domain (an $\mathbb F_2$-subspace) of size $N=16K$, where $K\ge2$ is a power of two. Let $\mathbb F\supsetneq\mathbb B$ be a finite field, and put
--
--   $$
--   M=\frac{(N-1)(N-2)}{6},
--   $$
--
--   the number of codimension-two subspaces of $D$. Codes, inputs and challenges are over $\mathbb F$, on $D$ viewed inside $\mathbb F$, at message length $K$. There is a pair $f,g:D\to\mathbb F$ such that
--
--   1. $\mathrm{agr}_K(f)\le 2K$ and $\mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=2K-1$;
--   2. there is one set $S\subseteq\mathbb F$ of exactly $M$ nonzero challenges with $\mathrm{Bad}_T(f,g)=S$ for every integer $2K+1\le T\le 4K-1$, and $\mathrm{agr}_K(f+zg)=4K-1=N/4-1$ for every $z\in S$;
--   3. $\mathrm{Bad}_{4K}(f,g)=\emptyset$.
--
--   If moreover $[\mathbb F:\mathbb B]\ge3$, there is a pair with all of these properties and $\mathrm{agr}_K(f)=2K-1$.
--
--   The Johnson radius $\sqrt{N(K-1)}$ lies strictly between $4K-3$ and $4K-2$, so the $M$ challenges are exceptional at the largest integer agreement below Johnson, on every binary additive domain, with both inputs far from the code.
--
--   **Formalization Note** $D$ is an additive subgroup of $\mathbb B$ of cardinality $16K$ (in characteristic two these are exactly the $\mathbb F_2$-subspaces); $\mathbb F\supsetneq\mathbb B$ is any finite field with an algebra map from $\mathbb B$ and $|\mathbb B|<|\mathbb F|$; $[\mathbb F:\mathbb B]$ is `Module.finrank`. $M$ is computed in $\mathbb N$ (it is an integer).
--
--   Differences from the source:
--   - encoding: D ⊆ B a binary additive domain of size N = 16K → D₀ : AddSubgroup B of a finite field of characteristic two with Nat.card D₀ = 16K; reason: in characteristic two the additive subgroups are exactly the F₂-subspaces; B is finite because it embeds in the finite field F
--   - encoding: F ⊋ B a finite field; inputs and challenges over F → a finite field F with Algebra B F and |B| < |F|; the code lives on pushDomain F D; reason: an algebra map of fields is injective, so this is a proper extension; the domain is D viewed inside F
--   - reading: for every 2K+1 ≤ T ≤ 4K−1, Bad_T(f, g) is the same set of M nonzero challenges, each with maximum agreement exactly 4K − 1 → ∃ S with |S| = M, 0 ∉ S, Bad_T = S for every such T, and agr_K(f + z g) = 4K − 1 for z ∈ S; reason: the literal content of item 2
--   - reading: if [F : B] ≥ 3, the pair can be chosen with agr_K(f) = 2K − 1 as well → when Module.finrank B F ≥ 3, one pair satisfying items 1–3 with agr_K(f) = 2K − 1; reason: 'as well' keeps all other properties of the pair
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 4.1, pp.26–27

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 4.1 (Quadratic count at rate 1/16)**, pp.26–27. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let D ⊆ B be a binary additive domain of size N = 16K, where K ≥ 2 is a power of two, and let
F ⊋ B be a finite field. Put M = (N − 1)(N − 2)/6, the number of codimension-two subspaces of D.
There is a pair f, g over F such that:
1. agr_K(f) ≤ 2K and agr_K(g) = CA_K(f, g) = 2K − 1;
2. for every integer 2K + 1 ≤ T ≤ 4K − 1, the set Bad_T(f, g) is the same set of M nonzero
challenges, and each of them has maximum agreement exactly 4K − 1 = N/4 − 1;
3. Bad_{4K}(f, g) is empty.
If [F : B] ≥ 3, the pair can be chosen with agr_K(f) = 2K − 1 as well."

**Formalization Note.**
* `B` is a finite field of characteristic two and `D` an additive subgroup `D₀ : AddSubgroup B`
  with `|D₀| = 16K` (a binary additive domain, Definition 3.7); `K = 2^j ≥ 2`.
* `F ⊋ B` is every finite field with `Algebra B F` and `|B| < |F|`; the code over `F` lives on the
  image `pushDomain F D` of `D`, and the inputs, codewords and challenges are over `F`.
* `M = (N − 1)(N − 2)/6` is computed in `ℕ`; it is an integer (`N` is a power of two, so `3`
  divides one of `N − 1`, `N − 2`, and one of them is even).
* Item 2 is one set `S` of `M` nonzero challenges with `Bad_T(f, g) = S` for every integer
  `T ∈ [2K + 1, 4K − 1]` and `agr_K(f + z g) = 4K − 1` for each `z ∈ S`.
* The last sentence is read as: when `[F : B] ≥ 3` (`Module.finrank B F ≥ 3`) there is one pair
  satisfying items 1–3 with `agr_K(f) = 2K − 1` in place of `agr_K(f) ≤ 2K`. -/
theorem theorem_4_1 {B : Type} [Field B] [Fintype B] [CharP B 2] (D₀ : AddSubgroup B) (K : ℕ)
    (hK2 : 2 ≤ K) (hKpow : ∃ j : ℕ, K = 2 ^ j) (hD : Nat.card D₀ = 16 * K)
    (F : Type) [Field F] [Fintype F] [Algebra B F] (hBF : Fintype.card B < Fintype.card F) :
    let N : ℕ := 16 * K
    let M : ℕ := (N - 1) * (N - 2) / 6
    let DF : Finset F := pushDomain F (domainFinset D₀)
    (∃ f g : DF → F,
      agr DF K f ≤ 2 * K ∧ agr DF K g = 2 * K - 1 ∧ CA DF K f g = 2 * K - 1 ∧
      (∃ S : Finset F, S.card = M ∧ (0 : F) ∉ S ∧
        (∀ T : ℕ, 2 * K + 1 ≤ T → T ≤ 4 * K - 1 → Bad DF K T f g = S) ∧
        ∀ z ∈ S, agr DF K (f + z • g) = 4 * K - 1) ∧
      Bad DF K (4 * K) f g = ∅) ∧
    (3 ≤ Module.finrank B F →
      ∃ f g : DF → F,
        agr DF K f = 2 * K - 1 ∧ agr DF K g = 2 * K - 1 ∧ CA DF K f g = 2 * K - 1 ∧
        (∃ S : Finset F, S.card = M ∧ (0 : F) ∉ S ∧
          (∀ T : ℕ, 2 * K + 1 ≤ T → T ≤ 4 * K - 1 → Bad DF K T f g = S) ∧
          ∀ z ∈ S, agr DF K (f + z • g) = 4 * K - 1) ∧
        Bad DF K (4 * K) f g = ∅) := by sorry

end GoldProxGap.Supplement
