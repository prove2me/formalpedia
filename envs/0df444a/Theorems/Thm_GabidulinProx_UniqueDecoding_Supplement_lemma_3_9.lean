-- Prove2me | Theorems.Thm_GabidulinProx_UniqueDecoding_Supplement_lemma_3_9
-- name    : GabidulinProx.UniqueDecoding.Supplement.lemma_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:42:37.627902+00:00
-- url     : https://prove2.me/theorems/02237a60-d98d-4f55-bc43-432a78a9aec3
-- title:
--   Lemma 3.9 — Weil's bound for multiplicative character sums
-- statement:
--   Let $F$ be a finite field with $|F|=M$ and let $\psi:F^*\to\mathbb C^*$ be a nontrivial multiplicative character of order $\ell>1$, extended to $F$ by $\psi(0)=0$. Let $f\in F[X]$ be nonconstant and assume that $f$ is not of the form $c\,g(X)^\ell$ with $c\in F^*$ and $g\in F[X]$. Let $s$ be the number of distinct roots of $f$ in its splitting field. Then
--
--   $$\Bigl|\sum_{x\in F}\psi\bigl(f(x)\bigr)\Bigr|\le (s-1)\sqrt M .$$
--
--   The bound holds for characters of every order, and $f$ need be neither monic nor squarefree. In the paper it gives the character-sum estimate behind the coefficient count of Lemma 3.10.
--
--   Differences from the source:
--   - encoding: a nontrivial character $\psi:F^*\to\mathbb C^*$ of order $\ell>1$ extended by $\psi(0)=0$ → `ψ : MulChar F ℂ` with `ψ ≠ 1`, and $\ell=$ `orderOf ψ`; reason: Mathlib's multiplicative characters vanish at non-units, which is the extension $\psi(0)=0$; a nontrivial element of the finite character group has order $>1$
--   - encoding: the number $s$ of distinct roots of $f$ in its splitting field → `(f.rootSet f.SplittingField).ncard`; reason: the root set of a nonzero polynomial is its finite set of distinct roots
-- source:
--   Songsong Li, Chaoping Xing, Chen Yuan, Ruiqi Zhu, Proximity Gaps for Gabidulin Codes and Applications, STOC 2027 submission #434 (October 2026), Lemma 3.9 p.24 (citing Lidl–Niederreiter 1997, Theorem 5.41). https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/434.pdf, SHA-256 8f644bcdfbdcd3478384d77d75a0f88ea116c29b14c52714f58bffb9ffda25cf

import Definitions.Def_GabidulinProx_UniqueDecoding_Supplement_Objects

namespace GabidulinProx.UniqueDecoding.Supplement

open GabidulinProx.UniqueDecoding

/-- Lemma 3.9, p.24 ([LN97, Theorem 5.41], Weil): for a nontrivial multiplicative character
`ψ` of a finite field `F` (with `ψ(0) = 0`) of order `ℓ`, and a nonconstant `f ∈ F[X]` that is
not of the form `c·g^ℓ` with `c ≠ 0`, if `s` is the number of distinct roots of `f` in its
splitting field then `|∑_{x∈F} ψ(f(x))| ≤ (s-1)√|F|`. -/
theorem lemma_3_9 {F : Type*} [Field F] [Fintype F] (ψ : MulChar F ℂ) (hψ : ψ ≠ 1)
    (f : Polynomial F) (hf : 0 < f.natDegree)
    (hpow : ¬ ∃ c : F, c ≠ 0 ∧ ∃ g : Polynomial F, f = Polynomial.C c * g ^ orderOf ψ) :
    ‖∑ x : F, ψ (f.eval x)‖ ≤
      (((f.rootSet f.SplittingField).ncard : ℝ) - 1) * Real.sqrt (Fintype.card F : ℝ) := by sorry
end GabidulinProx.UniqueDecoding.Supplement
