-- Prove2me | Theorems.Thm_FourierEntropyApprox_theorem_3_2_item_2
-- name    : FourierEntropyApprox.theorem_3_2_item_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T21:46:08.687611+00:00
-- url     : https://prove2.me/theorems/64a331b5-3750-43f1-a1bb-69018f450727
-- title:
--   Proof of Theorem 3.2, item 2: $\|\widehat{P_t}\|_1\le(1+\|\widehat P\|_1^2)^{t/2}$
-- statement:
--   Let $P:\{-1,1\}^n\to\mathbb R$ and $B=\|\widehat P\|_1$. For every $t\ge0$, the majority composition $P_t=\mathrm{Maj}_t(P,\dots,P)$ satisfies
--
--   $$\|\widehat{P_t}\|_1\le(1+B^2)^{t/2}.$$
--
--   This is the cost side of majority amplification: the spectral norm of $P_t$ grows at most exponentially in $t$, so $\log\max\{1,\|\widehat{P_t}\|_1\}$ grows linearly in $t$ times $\log(1+B)$. Combined with item 1 it gives approximants $Q_j=P_{4j+8}$ of accuracy $2^{-j}$ and log-spectral norm $O(j\log(1+B))$.
--
--   **Formalization Note** $P_t$ is `majCompose t P`, with ties of $\mathrm{Maj}_t$ at even $t$ going to $+1$.
--
--   Differences from the source:
--   - generalization: $P=3P'/4$ for a $1/3$-approximating $P'$ → every real $P$; reason: the page's bound uses no property of $P$; the statement specializes to the page's $P$
--   - generalization: $t\ge1$ variables → every $t\in\mathbb N$, including $t=0$; reason: $P_0\equiv1$ has spectral norm $1=(1+B^2)^0$; specializes to $t\ge1$
--   - reading: $\mathrm{Maj}_t$ at even $t$, tie rule unstated → ties go to $+1$; reason: the page uses even $t$; the bound holds for any $\pm1$-valued tie rule
--   - encoding: $\mathrm{Maj}_t(P,\dots,P)$ → the multilinear expansion of $\mathrm{Maj}_t$ evaluated at $(P(x),\dots,P(x))$; reason: the paper's meaning of the composition
--   - encoding: $\{-1,1\}^n$, $S\subseteq[n]$ → `Fin n → Bool` with true ↦ −1, `Finset (Fin n)`; reason: same points and sets
-- source:
--   Paraashar, Saurabh, Fourier Entropy Bounds via Approximations, arXiv:2611.06451 (held version, sha256 adc9c5fc…), proof of Theorem 3.2, item 2, p.16 (PDF p.16); B defined on p.15

import Mathlib
import Definitions.Def_FourierEntropyApprox_majCompose

namespace FourierEntropyApprox

/-- **Proof of Theorem 3.2, item 2 (spectral norm of the majority composition).** M. Paraashar, N. Saurabh, *Fourier Entropy Bounds via Approximations*, arXiv:2611.06451 (held version,
sha256 adc9c5fc…), p.16:
"2. ‖P̂_t‖₁ ≤ (1 + B²)^{t/2}", where `P_t = Maj_t(P, …, P)` and `B = ‖P̂‖₁` (p.15).

For every real function `P` on the cube and every `t`, the spectral norm of `P_t` is at most
`(1 + ‖P̂‖₁²)^{t/2}`.

**Formalization Note.** On the page `P = 3P′/4` for a 1/3-approximating `P′`; the bound is stated for every
real `P` and every `t` (including `t = 0`). `P_t` is `majCompose t P` (ties of `Maj_t` to `+1`). -/
theorem theorem_3_2_item_2 {n : ℕ} (P : Cube n → ℝ) (t : ℕ) :
    spectralNorm (majCompose t P) ≤ (1 + spectralNorm P ^ 2) ^ ((t : ℝ) / 2) := by sorry

end FourierEntropyApprox
