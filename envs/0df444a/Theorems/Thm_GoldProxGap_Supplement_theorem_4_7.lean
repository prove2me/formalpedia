-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_4_7
-- name    : GoldProxGap.Supplement.theorem_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:47:12.408616+00:00
-- url     : https://prove2.me/theorems/12a2a8c5-b652-469f-b3e0-401a27cea70b
-- title:
--   Theorem 4.7 — hyperplanes at half agreement: exactly $2N-2$ nonzero exceptional challenges at agreement $N/2$, rate $1/4$
-- statement:
--   **Theorem 4.7 (Hyperplanes at half agreement).** Let $\mathbb F$ be a finite field of characteristic two, and let $D\subsetneq\mathbb F$ be an affine flat (a translate of an $\mathbb F_2$-subspace) of size $N=2^d$, $d\ge3$. Put $K=N/4$. There is a pair $f,g:D\to\mathbb F$ with
--
--   $$
--   \mathrm{CA}_K(f,g)=K,\qquad \mathrm{agr}_K(f)\le \frac{3N}{8}-1,\qquad \mathrm{agr}_K(g)=K,\qquad |\mathrm{Bad}_{N/2}(f,g)|=2N-2,
--   $$
--
--   and all these exceptional challenges are nonzero. If $|\mathbb F|=2N$, then $\mathrm{Bad}_{N/2}(f,g)=\mathbb F\setminus\{0,s\}$ for some $s\ne0$, so the exceptional probability is exactly $1-1/N$.
--
--   At rate $1/4$, half agreement is the asymptotic Johnson threshold; the theorem shows that, over a field of size $2N$, almost every challenge is exceptional there although the pair has common agreement only $N/4$. Its received pair is reused by the constructions of Section 5.
--
--   **Formalization Note** $D=a+D_0$ with $D_0$ an additive subgroup of $\mathbb F$ of cardinality $2^d$; $D\subsetneq\mathbb F$ is $2^d<|\mathbb F|$. $K$, $N/2$ and $3N/8-1$ are exact natural numbers since $d\ge3$.
--
--   Differences from the source:
--   - encoding: D ⊊ F an affine flat of size N = 2^d → D = a + D₀ (translateDomain) with D₀ : AddSubgroup F, Nat.card D₀ = 2^d, and 2^d < |F|; reason: Definition 3.7: an affine flat is a translate of a linear (F₂-)subspace; in characteristic two additive subgroups are F₂-subspaces; properness is a cardinality condition
--   - reading: There is a pair … All these exceptional challenges are nonzero. If |F| = 2N, then Bad_{N/2}(f, g) = F \ {0, s} … → one pair with every listed property, including the |F| = 2N clause; reason: the later sentences describe the same pair
--   - encoding: giving exceptional probability exactly 1 − 1/N → |Bad_{N/2}(f, g)| / |F| = 1 − 1/N (in ℝ) when |F| = 2N; reason: the probability of a uniform challenge in F
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 4.7, p.33

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 4.7 (Hyperplanes at half agreement)**, p.33. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let F be a finite field of characteristic two, and let D ⊊ F be an affine flat of size N = 2^d,
d ≥ 3. Put K = N/4. There is a pair with inputs and challenges in F satisfying
CA_K(f, g) = K, agr_K(f) ≤ 3N/8 − 1, agr_K(g) = K, and |Bad_{N/2}(f, g)| = 2N − 2.
All these exceptional challenges are nonzero. If |F| = 2N, then Bad_{N/2}(f, g) = F \ {0, s} for
some s ≠ 0, giving exceptional probability exactly 1 − 1/N."

**Formalization Note.**
* An affine flat of size `2^d` is `D = a + D₀` with `D₀ : AddSubgroup F`, `|D₀| = 2^d`
  (Definition 3.7; in characteristic two an additive subgroup is an `F₂`-subspace).
  `D ⊊ F` is `2^d < |F|`.
* `K = N/4`, `N/2` and `3N/8 − 1` are exact natural numbers (`d ≥ 3`).
* "One pair" with all the listed properties at once; the exceptional probability
  `|Bad_{N/2}|/|F| = 1 − 1/N` when `|F| = 2N` is stated as a conjunct. -/
theorem theorem_4_7 {F : Type} [Field F] [Fintype F] [CharP F 2] (D₀ : AddSubgroup F) (d : ℕ)
    (hd : 3 ≤ d) (hD : Nat.card D₀ = 2 ^ d) (a : F) (hproper : 2 ^ d < Fintype.card F) :
    let N : ℕ := 2 ^ d
    let K : ℕ := N / 4
    let Dom : Finset F := translateDomain a (domainFinset D₀)
    ∃ f g : Dom → F,
      CA Dom K f g = K ∧ agr Dom K f ≤ 3 * N / 8 - 1 ∧ agr Dom K g = K ∧
      (Bad Dom K (N / 2) f g).card = 2 * N - 2 ∧ (0 : F) ∉ Bad Dom K (N / 2) f g ∧
      (Fintype.card F = 2 * N →
        (∃ s : F, s ≠ 0 ∧ Bad Dom K (N / 2) f g = Finset.univ \ {0, s}) ∧
        ((Bad Dom K (N / 2) f g).card : ℝ) / (Fintype.card F : ℝ) = 1 - 1 / (N : ℝ)) := by sorry

end GoldProxGap.Supplement
