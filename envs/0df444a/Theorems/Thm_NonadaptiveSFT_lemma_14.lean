-- Prove2me | Theorems.Thm_NonadaptiveSFT_lemma_14
-- name    : NonadaptiveSFT.lemma_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:23:38.22946+00:00
-- url     : https://prove2.me/theorems/61b8e0a9-25d5-4739-bd7b-7f4b72ac5400
-- title:
--   Lemma 14 — least squares on $n_{ls}=170s\lceil\log(2040s)\rceil$ samples: a polynomial-time fit, and residual norm bounds (28)–(29) for all $S\subseteq\Omega$ w.p. $1-1/30$
-- statement:
--   Assume $\sigma_s(\widehat X)_2^2\le s\tau^2$ with $\tau\ge0$, and let $\Omega$, $\bar\sigma$, $n_{ls}$, $A$, $b$, $b_{ls}=\sqrt{255}/2$, $\delta_{ls}=1/30$, $C_S$, $z_S$ and $M_S$ be as in the least-squares definitions. Then:
--
--   1. there is a polynomial-time algorithm which either aborts or computes $C_S$ and $M_S$ from the samples $t_1,\dots,t_{n_{ls}}$ (with their outcomes $X(t_b)$), the set $S\subseteq G$ and $\bar\sigma$;
--   2. with probability at least $1-\delta_{ls}$ over uniform independent samples, for all $S\subseteq\Omega$ simultaneously,
--
--   $$\|\widehat X-C_S\|_2\le\sqrt2(\|z_S\|_2+b_{ls}\bar\sigma)+\|\widehat X_{G\setminus\Omega}\|_2,\qquad\|z_S\|_2\le\sqrt{3/2}\,\|\widehat X_{\Omega\setminus S}\|_2+b_{ls}\bar\sigma,\tag{28}$$
--
--   $$\|\widehat X-C_S\|_2\le M_S,\qquad M_S^2\le12\|\widehat X_{\Omega\setminus S}\|_2^2+50b_{ls}^2\bar\sigma^2.\tag{29}$$
--
--   $\Omega$ is fixed independently of the sample, while the supports $S\subseteq\Omega$ may depend on it. The certificate $M_S$ is the computable norm promise that every locator call receives.
--
--   **Formalization Note** The algorithm is a program of the machine taking the samples, their outcomes, the listed elements of $S$ and $\bar\sigma$; it halts within $C(n_{ls}+|S|+ad)^K$ steps on every input, aborts exactly when $A_S^*A_S$ is singular, and otherwise outputs $C_S$ and $M_S$ exactly.
--
--   Differences from the source:
--   - encoding: a polynomial-time algorithm → one admissible program of NonadaptiveSFT.Machine halting within C(n_ls + |S| + ad)^K steps on every input, oracle and tape; reason: the paper's exact arithmetic model; input size is measured by the numbers of samples, listed frequencies and coordinates
--   - reading: either aborts or computes C_S, M_S → aborts exactly when A_S^*A_S is singular, otherwise outputs C_S and M_S exactly; reason: the proof's routine (p.30); a routine allowed to abort at will would make the clause empty
--   - reading: the following holds for all S ⊆ Ω simultaneously: (28), (29) → for all S ⊆ Ω: A_S^*A_S is nonsingular and (28), (29) hold; reason: C_S is the argmin only when it is unique; the proof establishes nonsingularity on the same event (p.31)
--   - reading: s (no range stated in §5) → every integer s ≥ 1; reason: §5 assumes only (33); §6's 2 ≤ s < N is not used by the lemma
--   - encoding: probability over uniform and independent samples → proportion of tuples in G^{n_ls}; reason: the uniform product law on a finite set
-- source:
--   Cheraghchi, Lyu, A Nonadaptive Sparse Fourier Transform in Every Dimension, STOC 2027 submission (manuscript sha256 b9a0e055…), Lemma 14, p.30, and its proof, pp.30–32 (PDF pp.32–34); §5 preamble, p.30

import Mathlib
import Definitions.Def_NonadaptiveSFT_Machine
import Definitions.Def_NonadaptiveSFT_LeastSquares

namespace NonadaptiveSFT

/-- **Lemma 14** (Simultaneous residual norm bounds from least squares), p.30 (PDF p.32).

M. Cheraghchi, J. Lyu, *A Nonadaptive Sparse Fourier Transform in Every Dimension*, STOC 2027
submission (manuscript sha256 b9a0e055…); §5 preamble ("we assume the tail-norm bound (33), i.e.,
σ_s(X̂)₂² ≤ sτ², where τ ≥ 0"), p.30.

With `Ω = {f : |X̂(f)| > τ/4}`, `σ̄ = √s τ`, `n_ls = 170s⌈log(2040s)⌉` samples, `A_{bf} = χ_f(t_b)/√n_ls`,
`b_b = X(t_b)/√n_ls`, `b_ls = √255/2`, `δ_ls = 1/30`, `C_S` the least-squares fit on `A_S` (`C_∅ = 0`),
`z_S = b − A_S C_S`, `M_S = 2‖z_S‖₂ + 3b_ls σ̄`:
1. there is a polynomial-time algorithm which either aborts or computes `C_S`, `M_S` from the samples
   `t_1, …, t_{n_ls}`, the set `S ⊆ G` and `σ̄`;
2. with probability at least `1 − δ_ls` over uniform independent samples, (28) and (29) hold for
   all `S ⊆ Ω` simultaneously.

**Formalization Note.**
* Clause 1 is posed on `NonadaptiveSFT.Machine` with input `lsInit` (samples, sample outcomes
  `X(t_b)`, the listed elements of `S`, `σ̄`, the root of unity). On every input, oracle and tape it
  halts within `C(n_ls + |S| + ad)^K` steps (polynomial time; `C`, `K` absolute); it aborts exactly
  when `A_S^*A_S` is singular (proof, p.30: "If A_S^*A_S is singular, the algorithm aborts"), and
  otherwise outputs `C_S` (decoded output list `0`) and `M_S` (scalar output) exactly. An algorithm
  that may abort at will would make "either aborts or computes" empty.
* Clause 2: `LSGood` is the event "for every `S ⊆ Ω`, `A_S^*A_S` is nonsingular and (28), (29) hold";
  the quantifier over `S` is inside the event, and `Ω` depends on `X̂` and `τ` only. Nonsingularity
  makes `C_S` the unique fit (proof, p.31: "On E1, for any S ⊆ Ω, the matrix A_S^*A_S is
  nonsingular").
* `s ≥ 1` is a positive integer; §6's `2 ≤ s < N` is not assumed in §5. `σ_s` is computed with the
  lexicographic tie order (its value does not depend on the order). -/
theorem lemma_14 :
    (∃ (P : Program) (_ : Admissible P) (C : ℝ) (K : ℕ), 0 < C ∧
      ∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (s : ℕ), 1 ≤ s →
      ∀ (X : G a d → ℂ) (U : Fin (nls s) → G a d) (Sl : List (G a d)), Sl.Nodup →
      ∀ (σbar : ℝ) (X' : G a d → ℂ) (ω : ℕ → Bool),
        let S := Sl.toFinset
        let s₀ := lsInit U (fun b => X (U b)) Sl σbar
        ∃ m : ℕ, (run P X' s₀ ω m).halted = true ∧
          ((run P X' s₀ ω m).work : ℝ) ≤ C * ((nls s + Sl.length + a * d : ℕ) : ℝ) ^ K ∧
          (aborted (run P X' s₀ ω m) ↔ (gram U S).det = 0) ∧
          ((gram U S).det ≠ 0 →
            outVec (run P X' s₀ ω m) 0 = fit X U S ∧
            outScalar (run P X' s₀ ω m) = Mval X U S σbar)) ∧
    (∀ (a d : ℕ), 1 ≤ a → 1 ≤ d → ∀ (s : ℕ), 1 ≤ s → ∀ (τ : ℝ), 0 ≤ τ →
      ∀ X : G a d → ℂ, sigma (lexKey a d) s (hat X) ^ 2 ≤ s * τ ^ 2 →
        1 - 1 / 30 ≤ sampleProb (nls s) (fun U => LSGood X U s τ)) := by sorry

end NonadaptiveSFT
