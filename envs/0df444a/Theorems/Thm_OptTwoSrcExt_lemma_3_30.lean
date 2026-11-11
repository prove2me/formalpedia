-- Prove2me | Theorems.Thm_OptTwoSrcExt_lemma_3_30
-- name    : OptTwoSrcExt.lemma_3_30
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:25:06.012642+00:00
-- url     : https://prove2.me/theorems/3bac5f47-51fb-4740-8ded-c8d341023eb2
-- title:
--   Lemma 3.30 — a forest of moment secants: $\dim_{\mathbb F_2}\mathrm{span}\{w(x)\}\ge\log\binom{\lfloor|A|/3\rfloor}{p}$
-- statement:
--   Let $K$ be a field of characteristic two, $A\subseteq K$ finite, and $f:A\to K$ with $f(x)\ne x$ for all $x\in A$. For nonzero $a,b\in K$ put
--   $$v_L(x)=(1,x,\dots,x^{L-1}),\qquad w(x)=a\,v_L(x)+b\,v_L(f(x))\in K^L .$$
--   If $4p\le L$ and $|A|\ge\max\{12,4p\}$, then
--   $$\dim_{\mathbb F_2}\operatorname{span}_{\mathbb F_2}\{w(x):x\in A\}\ \ge\ \log\binom{\lfloor|A|/3\rfloor}{p}\ \ge\ p\log|A|-p\log(4p).$$
--   Logarithms are base 2 and $K$ need not be finite.
--
--   This rank lower bound for secant vectors drives the restricted-rank bound of Proposition 3.31 against one-sided tampering.
--
--   **Formalization Note** "Characteristic two" is an $\mathbb F_2$-algebra structure on $K$, which makes $K^L$ an $\mathbb F_2$-vector space; $f$ is a map $K\to K$ whose values off $A$ are not used.
--
--   Differences from the source:
--   - encoding: K a field of characteristic two; f : A → K → [Field K] [Algebra (ZMod 2) K]; f : K → K with f(x) ≠ x for x ∈ A; reason: a field has an F_2-algebra structure exactly when its characteristic is two; values of f off A do not occur
-- source:
--   X. Li, Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate, STOC 2027 submission (manuscript sha256 2edb00b2…), Lemma 3.30, p.47 (PDF p.49)

import Mathlib

namespace OptTwoSrcExt

/-- **Lemma 3.30 (A forest of moment secants).**
Li, *Asymptotically Optimal Two Source Extractors for Arbitrary Constant Entropy Rate*, STOC 2027
submission (manuscript sha256 2edb00b2…), Lemma 3.30, printed p.47 (PDF p.49): "Let A be a finite
subset of a field K of characteristic two and f : A → K satisfy f(x) ≠ x. For nonzero a, b ∈ K, put
vL(x) = (1, x, . . . , x^{L−1}), w(x) = a vL(x) + b vL(f(x)). If 4p ⩽ L and |A| ⩾ max{12, 4p}, then
dim_{F2} span{w(x) : x ∈ A} ⩾ log (⌊|A|/3⌋ choose p) ⩾ p log |A| − p log(4p)."

Let `K` be a field of characteristic two, `A ⊆ K` finite, `f` a map with `f(x) ≠ x` for `x ∈ A`, and
`a, b ∈ K` nonzero. With `v_L(x) = (1, x, …, x^{L−1}) ∈ K^L` and `w(x) = a·v_L(x) + b·v_L(f(x))`, if
`4p ≤ L`, `|A| ≥ 12` and `|A| ≥ 4p`, then
`dim_{𝔽₂} span_{𝔽₂}{w(x) : x ∈ A} ≥ log₂ C(⌊|A|/3⌋, p) ≥ p log₂|A| − p log₂(4p)`.

**Formalization Note.** "Characteristic two" is an `𝔽₂`-algebra structure `[Algebra (ZMod 2) K]`
(a field admits one exactly when its characteristic is two, and it is then unique); it makes `K^L`
an `𝔽₂`-vector space, and the span is the `𝔽₂`-span inside `K^L`. `K` need not be finite. The map
`f : A → K` is a map `K → K` whose values off `A` are never used. Logarithms are base 2; `p, L` are
natural numbers. -/
theorem lemma_3_30 {K : Type*} [Field K] [Algebra (ZMod 2) K] (A : Finset K) (f : K → K)
    (hf : ∀ x ∈ A, f x ≠ x) (a b : K) (ha : a ≠ 0) (hb : b ≠ 0) (L p : ℕ) (hpL : 4 * p ≤ L)
    (hA12 : 12 ≤ A.card) (hAp : 4 * p ≤ A.card) :
    Real.logb 2 ((A.card / 3).choose p) ≤
        (Module.finrank (ZMod 2) (Submodule.span (ZMod 2)
          ((fun x : K => fun i : Fin L => a * x ^ (i : ℕ) + b * f x ^ (i : ℕ)) '' (A : Set K))) : ℝ) ∧
      (p : ℝ) * Real.logb 2 A.card - p * Real.logb 2 (4 * p) ≤
        Real.logb 2 ((A.card / 3).choose p) := by sorry

end OptTwoSrcExt
