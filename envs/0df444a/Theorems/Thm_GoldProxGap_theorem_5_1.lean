-- Prove2me | Theorems.Thm_GoldProxGap_theorem_5_1
-- name    : GoldProxGap.theorem_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:22:47.365964+00:00
-- url     : https://prove2.me/theorems/f20bc7f2-26e0-4420-a854-8cf588b7832e
-- title:
--   Theorem 5.1 — the Gold counting bound: $L=2^{2t}(2^\Delta-1)[\lfloor d/2\rfloor\ t]_4$ codewords and $Z$ nonzero exceptional challenges at $T=N/2-N/2^{t+1}$
-- statement:
--   **Theorem 5.1 (The Gold counting bound).** Let $\mathbb B=\mathbb F_{2^m}$ and let $D\subseteq\mathbb B$ be binary additive of dimension $d$, $N=2^d$. Choose $2\le t\le\lfloor d/2\rfloor$, put $\iota=1$ for even $d$ and $\iota=0$ for odd $d$, and suppose $\Delta=m-t(m-d+\iota)\ge1$. Set
--   $$
--   L=2^{2t}(2^\Delta-1)\begin{bmatrix}\lfloor d/2\rfloor\\ t\end{bmatrix}_4,\qquad T=\frac N2-\frac N{2^{t+1}},\qquad \delta=\frac N{2^{2t}} .
--   $$
--   1. **Decoding list.** Some received word $w:D\to\mathbb B$ has at least $L$ codewords of message length $N/4$ at agreement $T$.
--   2. **Exceptional challenges.** For every finite extension $\mathbb F\supseteq\mathbb B$ with $q=|\mathbb F|>N$ there is one received pair $f,g$ over $\mathbb F$ with $\mathrm{agr}_{N/4}(g)=\mathrm{CA}_{N/4}(f,g)=N/4$ and $\mathrm{agr}_{N/4}(f)\le 3N/8-1$, and a set of at least
--   $$
--   Z=\max\Bigl\{L-\Bigl\lfloor\frac{\delta\binom L2}{q-N}\Bigr\rfloor,\ \Bigl\lceil\frac{L(q-N)}{q-N+\delta(L-1)}\Bigr\rceil\Bigr\}\ \ge\ \frac12\min\Bigl\{L,\frac{q-N}\delta\Bigr\}
--   $$
--   distinct nonzero exceptional challenges at agreement $T$, each with an explaining polynomial of degree at most $T/2-1$ on at least $T$ points.
--
--   The same conclusions hold on every affine translate $a+D$.
--
--   This is the engine of the dense-domain counterexamples: a superpolynomial family of polynomials sharing their high coefficients gives a large decoding list and, after a pole reduction and collision averaging, a pair with common agreement exactly $N/4$ but many exceptional challenges just below the Johnson agreement $N/2$.
--
--   **Formalization Note** $L$ and $Z$ are real numbers, $\binom L2=L(L-1)/2$, $\Delta$ is an integer, and $[a\ b]_4$ is the product formula `gaussBinom`. The domain is $a+D_0$ for an additive subgroup $D_0$; the code over $\mathbb F$ lives on the image of $a+D_0$ in $\mathbb F$.
--
--   Differences from the source:
--   - encoding: B = F_{2^m} → every field B with 2^m elements; reason: finite fields of the same size are isomorphic
--   - encoding: D binary additive of dimension d; "the same conclusions hold on every affine translate of D" → the domain is a + D₀ for every a ∈ B and every additive subgroup D₀ with 2^d elements; reason: a = 0 is the linear case; the clause on affine translates is part of the statement
--   - encoding: finite extension F ⊇ B, q = |F| → every finite field F with Algebra B F, q = Fintype.card F, code on the image of the domain in F; reason: same objects
--   - encoding: L, Z with (L choose 2), Δ → real L and Z, (L choose 2) = L(L − 1)/2, integer Δ, [⌊d/2⌋ t]₄ = gaussBinom 4 (d/2) t; reason: L is a natural number, so L(L − 1)/2 is its binomial coefficient
--   - reading: there is one received pair … The pair can also be chosen with agr_{N/4}(f) ≤ 3N/8 − 1 → one pair (f, g) satisfying all the agreement conditions at once; reason: the stronger of the two readings; the proof's final pair satisfies all of them
--   - reading: at least Z distinct nonzero exceptional challenges …, and at least Z of them admit explaining polynomials of degree at most T/2 − 1 → one set S of nonzero exceptional challenges with |S| ≥ Z, each with a polynomial of degree ≤ T/2 − 1 agreeing with f + zg on ≥ T points; reason: this implies both counts
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9cedf047e9f98d174f41e6742e827f7c6f0e1dd00939b3975e7fe66f4e4d), Theorem 5.1, pp.34–35 (printed = PDF pages 34–35)

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap

/-- **Theorem 5.1 (The Gold counting bound)**, pp.34–35. Dao, Kominers, Thaler, Zheng,
*Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027 submission
manuscript (2 November 2026, sha256 6c2d9ced…).

"Let B = F_{2^m} and let D ⊆ B be binary additive of dimension d, with N = 2^d. Choose
2 ≤ t ≤ ⌊d/2⌋, put ι = 1 for even d and ι = 0 for odd d, and suppose Δ = m − t(m − d + ι) ≥ 1. Set
L = 2^{2t}(2^Δ − 1)[⌊d/2⌋ t]₄, T = N/2 − N/2^{t+1}, δ = N/2^{2t}. […]
1. Decoding list. Some received word over B has at least L codewords of message length N/4 at
agreement T.
2. Exceptional challenges. For every finite extension F ⊇ B with q = |F| > N, there is one
received pair over F with agr_{N/4}(g) = CA_{N/4}(f, g) = N/4 and at least
Z = max{L − ⌊δ·(L choose 2)/(q − N)⌋, ⌈L(q − N)/(q − N + δ(L − 1))⌉} ≥ (1/2) min{L, (q − N)/δ} (5.1)
distinct nonzero exceptional challenges at agreement T, and at least Z of them admit explaining
polynomials of degree at most T/2 − 1. The pair can also be chosen with agr_{N/4}(f) ≤ 3N/8 − 1.
The same conclusions hold on every affine translate of D."

**Formalization Note.**
* `B = F_{2^m}` is every field with `2^m` elements; `D = a + D₀` with `D₀ : AddSubgroup B`,
  `|D₀| = 2^d` (the linear case is `a = 0`; this carries "every affine translate").
* `F ⊇ B` is every finite field with `Algebra B F`; the code over `F` lives on the image of `D`.
* `Δ` is an integer; `L`, `Z` are real numbers (`[⌊d/2⌋ t]₄ = gaussBinom 4 (d/2) t`), with
  `(L choose 2) = L(L − 1)/2`. `T`, `δ`, `N/4`, `3N/8` are exact natural numbers here
  (`4 ≤ 2t ≤ d`).
* "One received pair … The pair can also be chosen with …" is read as one pair `(f, g)` with all
  the stated properties at once. "At least Z distinct nonzero exceptional challenges …, and at
  least Z of them admit explaining polynomials of degree at most T/2 − 1" is one set `S` of
  nonzero exceptional challenges (`T ≤ agr_{N/4}(f + z g)`, the defining condition of
  `z ∈ Bad_T(f, g)`) with `|S| ≥ Z`, each with a polynomial of degree `≤ T/2 − 1`
  agreeing with `f + z g` on at least `T` points. The inequality in (5.1) is a conclusion. -/
theorem theorem_5_1 {B : Type} [Field B] [Fintype B] (m : ℕ) (hB : Fintype.card B = 2 ^ m)
    (D₀ : AddSubgroup B) (d : ℕ) (hD : Nat.card D₀ = 2 ^ d) (a : B) (t : ℕ) (ht : 2 ≤ t)
    (htd : t ≤ d / 2)
    (hΔ : 1 ≤ (m : ℤ) - (t : ℤ) * ((m : ℤ) - (d : ℤ) + (if Even d then 1 else 0))) :
    let N : ℕ := 2 ^ d
    let Δ : ℤ := (m : ℤ) - (t : ℤ) * ((m : ℤ) - (d : ℤ) + (if Even d then 1 else 0))
    let L : ℝ := (2 : ℝ) ^ (2 * t) * ((2 : ℝ) ^ Δ - 1) * HScattered.Hyperplanes.gaussBinom 4 (d / 2) t
    let T : ℕ := N / 2 - N / 2 ^ (t + 1)
    let δ : ℕ := N / 2 ^ (2 * t)
    let Dom : Finset B := translateDomain a (domainFinset D₀)
    (∃ w : Dom → B, L ≤ ((decodingList Dom (N / 4) T w).card : ℝ)) ∧
    ∀ (F : Type) [Field F] [Fintype F] [Algebra B F], N < Fintype.card F →
      let q : ℝ := Fintype.card F
      let DF : Finset F := pushDomain F Dom
      let Z : ℝ := max (L - (⌊(δ : ℝ) * (L * (L - 1) / 2) / (q - N)⌋ : ℝ))
        (⌈L * (q - N) / (q - N + (δ : ℝ) * (L - 1))⌉ : ℝ)
      (1 / 2 : ℝ) * min L ((q - N) / δ) ≤ Z ∧
      ∃ f g : DF → F,
        agr DF (N / 4) g = N / 4 ∧ CA DF (N / 4) f g = N / 4 ∧ agr DF (N / 4) f ≤ 3 * N / 8 - 1 ∧
        ∃ S : Finset F, (0 : F) ∉ S ∧ Z ≤ (S.card : ℝ) ∧
          ∀ z ∈ S, T ≤ agr DF (N / 4) (f + z • g) ∧
            ∃ h : F[X], h.degree ≤ ((T / 2 - 1 : ℕ) : WithBot ℕ) ∧ T ≤ polyAgree (f + z • g) h := by sorry

end GoldProxGap
