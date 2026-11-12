-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_2_Qj
-- name    : FourierEntropyApprox.theorem_3_2_Qj
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:46:20.190744+00:00
-- url     : https://prove2.me/theorems/fc53af8c-bfff-42d7-b985-a487b31bd875
-- title:
--   Proof of Theorem 3.2, the approximants $Q_j=P_{4j+8}$: $\|f-Q_j\|_2^2\le2^{-j}$ and $\log\max\{1,\|\widehat{Q_j}\|_1\}=O(j\log(1+B))$
-- statement:
--   Let $f:\{-1,1\}^n\to\{-1,1\}$ be Boolean and let $P'$ be a $1/3$-approximating polynomial for $f$, i.e. $|P'(x)-f(x)|\le1/3$ for every $x$. Put $P=3P'/4$, $B=\|\widehat P\|_1$, $P_t=\mathrm{Maj}_t(P,\dots,P)$, and for $j\ge1$
--
--   $$Q_j=P_{4j+8}.$$
--
--   There is an absolute constant $c>0$ such that for every such $n$, $f$, $P'$ and every $j\ge1$,
--
--   $$\|f-Q_j\|_2^2\le2^{-j}\qquad\text{and}\qquad \log_2\max\{1,\|\widehat{Q_j}\|_1\}\le c\,j\log_2(1+B).$$
--
--   These are the approximants to which the proof of Theorem 3.2 applies Theorem 3.1, with $a=1$ and $L$ proportional to $\log(1+B)$.
--
--   **Formalization Note** The $O(\cdot)$ of the page is an absolute constant $c$, chosen before $n$, $f$, $P'$ and $j$. Logarithms are to base two (p.2).
--
--   Differences from the source:
--   - reading: $\log\max\{1,\|\widehat{Q_j}\|_1\}\le O(j\log(1+B))$ → there is an absolute $c>0$, chosen before $n$, $f$, $P'$, $j$, with $\log_2\max\{1,\|\widehat{Q_j}\|_1\}\le c\,j\log_2(1+B)$; reason: Theorem 3.1 is applied with one constant for all $j$ and all $f$
--   - reading: $\mathrm{Maj}_t$ at even $t$, tie rule unstated → ties go to $+1$; reason: $t=4j+8$ is even; items 1 and 2 hold for either tie value
--   - encoding: $\mathrm{Maj}_t(P,\dots,P)$ → the multilinear expansion of $\mathrm{Maj}_t$ evaluated at $(P(x),\dots,P(x))$; reason: the paper's meaning of the composition
--   - encoding: $\{-1,1\}^n$, $S\subseteq[n]$ → `Fin n → Bool` with true ↦ −1, `Finset (Fin n)`; reason: same points and sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), proof of Theorem 3.2, display after item 2, p.16 (PDF p.16); setting p.15

import Mathlib
import Definitions.Def_FourierEntropyApprox_IsBoolean
import Definitions.Def_FourierEntropyApprox_majCompose

namespace FourierEntropyApprox

/-- **Proof of Theorem 3.2, the approximants `Q_j`.** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.16:
"For each j ≥ 1, define the approximant Q_j := P_{4j+8}. We, therefore, have ‖f − Q_j‖₂² ≤ 2^{−j}, and
log max{1, ‖Q̂_j‖₁} ≤ O(j log(1 + B))." Context, p.15: `f` Boolean, `P′` a 1/3-approximating polynomial
for `f`, `P := 3P′/4`, `P_t := Maj_t(P, …, P)`, `B := ‖P̂‖₁`.

There is an absolute constant `c > 0` such that for every `n`, every Boolean `f`, every real `P′` with
`|P′(x) − f(x)| ≤ 1/3` at every `x`, and every `j ≥ 1`, with `P = 3P′/4` and `Q_j = P_{4j+8}`:
`‖f − Q_j‖₂² ≤ 2^{−j}` and `log₂ max{1, ‖Q̂_j‖₁} ≤ c · j · log₂(1 + ‖P̂‖₁)`.

**Formalization Note.** The `O(·)` is an absolute constant `c`, chosen before `n`, `f`, `P′` and `j`.
`2^{−j}` is `((2 : ℝ) ^ j)⁻¹`; logarithms are base two (p.2). -/
theorem theorem_3_2_Qj :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (f P' : Cube n → ℝ), IsBoolean f → (∀ x, |P' x - f x| ≤ 1 / 3) →
      ∀ j : ℕ, 1 ≤ j →
        l2NormSq (f - majCompose (4 * j + 8) (fun x => 3 * P' x / 4)) ≤ ((2 : ℝ) ^ j)⁻¹ ∧
          Real.logb 2 (max 1 (spectralNorm (majCompose (4 * j + 8) (fun x => 3 * P' x / 4)))) ≤
            c * j * Real.logb 2 (1 + spectralNorm (fun x => 3 * P' x / 4)) := by sorry

end FourierEntropyApprox
