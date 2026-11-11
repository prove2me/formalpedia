-- Prove2me | Theorems.Thm_LLROPI_Shamir_lemma_2_9
-- name    : LLROPI.Shamir.lemma_2_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:33:00.870202+00:00
-- url     : https://prove2.me/theorems/5cd755fd-353c-44b6-9397-6c1b22194db9
-- title:
--   Lemma 2.9 — Cauchy–Schwarz step: $|\mathbb E\,GP|^2\le\mathbb E_{x,\,h\in K}P(x)\overline{P(x+h)}$ for a 1-bounded $K$-invariant $G$
-- statement:
--   Let $G,P:\mathbb F_p^k\to\mathbb C$, and suppose $G$ is $K$-invariant for some subspace $K\le\mathbb F_p^k$, i.e. $G(x+h)=G(x)$ for every $x\in\mathbb F_p^k$ and $h\in K$, and $1$-bounded, $\|G\|_\infty\le1$. Then
--   $$\Big|\mathbb E_{x\in\mathbb F_p^k}G(x)P(x)\Big|^2\le\mathbb E_{x\in\mathbb F_p^k,\ h\in K}P(x)\overline{P(x+h)}=:\mathbb E_{x,h}\Delta_hP(x).\qquad(2.6)$$
--   In the formal statement the right-hand side is the complex average; the inequality asserts that it is real (imaginary part $0$) and that its real part dominates the left-hand side.
--
--   Differences from the source:
--   - encoding: the inequality |E G P|² ≤ E_{x,h} P(x) conj(P(x + h)) between a real number and a complex average → the average has imaginary part 0 and |E G P|² ≤ its real part; reason: the printed ≤ asserts that the right-hand side is real; both parts are stated
-- source:
--   Sun, Wootters, Improved Local Leakage Resilience of Shamir Secret Sharing and Worst-Case Optimal Polynomial Intersection, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.9, (2.6), p. 23 (PDF 25)

import Mathlib

namespace LLROPI.Shamir

open Classical in
/-- **Lemma 2.9**, p. 23 (PDF 25). For any `G, P : 𝔽_p^k → ℂ`, suppose `G` is `K`-invariant for
some subspace `K ≤ 𝔽_p^k` (`G(x + h) = G(x)` for every `x` and `h ∈ K`) and `1`-bounded
(`‖G‖_∞ ≤ 1`). Then
`|E_{x ∈ 𝔽_p^k} G(x) P(x)|² ≤ E_{x ∈ 𝔽_p^k, h ∈ K} P(x) \overline{P(x + h)}`.
Sun, Wootters, arXiv:2610.12357 (held version, sha256 f154f5ce…), Lemma 2.9, (2.6), p. 23 (PDF 25).

**Formalization Note.** The right-hand side is a complex average; the inequality asserts that it is
real (imaginary part `0`) and at least the left-hand side. Expectations are normalized sums over
`𝔽_p^k` and over the finite set of elements of `K`. -/
theorem lemma_2_9 (p : ℕ) [Fact p.Prime] (k : ℕ) (G P : (Fin k → ZMod p) → ℂ)
    (K : Submodule (ZMod p) (Fin k → ZMod p))
    (hinv : ∀ x, ∀ h ∈ K, G (x + h) = G x) (hbdd : ∀ x, ‖G x‖ ≤ 1) :
    ((∑ x : Fin k → ZMod p, ∑ h ∈ Finset.univ.filter (fun h => h ∈ K), P x * star (P (x + h))) /
        ((p : ℂ) ^ k * ((Finset.univ.filter (fun h => h ∈ K)).card : ℂ))).im = 0 ∧
    ‖(∑ x : Fin k → ZMod p, G x * P x) / (p : ℂ) ^ k‖ ^ 2 ≤
      ((∑ x : Fin k → ZMod p, ∑ h ∈ Finset.univ.filter (fun h => h ∈ K), P x * star (P (x + h))) /
        ((p : ℂ) ^ k * ((Finset.univ.filter (fun h => h ∈ K)).card : ℂ))).re := by sorry

end LLROPI.Shamir
