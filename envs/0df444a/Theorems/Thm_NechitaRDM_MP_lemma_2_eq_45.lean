-- Prove2me | Theorems.Thm_NechitaRDM_MP_lemma_2_eq_45
-- name    : NechitaRDM.MP.lemma_2_eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:45.144245+00:00
-- url     : https://prove2.me/theorems/4187d464-9b56-48a1-b5a6-f7676ddfb800
-- title:
--   Lemma 2, (45), p. 13 — the trace Sₙ of a Wishart matrix of parameters n and k(n) satisfies Sₙ/(nk(n)) → 1 almost surely
-- statement:
--   Let $c \in (0,\infty)$ and let $(k(n))_n$ be integers with $\lim_{n\to\infty} k(n)/n = c$. For every $n$ let $W_n = X_n X_n^*$ be a Wishart matrix of parameters $n$ and $k(n)$, and let $S_n = \operatorname{Tr} W_n$. Then
--   $$\frac{S_n}{n\,k(n)} \longrightarrow 1 \qquad \text{almost surely.}$$
--
--   The trace $S_n = \sum_{i,j} |X_n(i,j)|^2$ is the normalizing factor relating $\rho_n = W_n / S_n$ to $W_n$; this lemma shows that the factor $cn^2/S_n$ in eq. (51) tends to $1$.
--
--   **Formalization Note** Only the almost sure part (45) of Lemma 2 is stated; the central limit theorem (46) is used only for the largest eigenvalue (Theorem 6). Nothing is assumed about the joint law of the $X_n$ across $n$; the claim holds for every coupling. $S_n$ is the real part of the trace (the trace is real and nonnegative). For the finitely many $n$ with $n\,k(n) = 0$ the ratio is $0$ in Lean, which does not affect the limit.
-- source:
--   Nechita, Asymptotics of random density matrices, arXiv:quant-ph/0702154v3, p. 13, Lemma 2, eq. (45)

import Mathlib
import Definitions.Def_NechitaRDM_MP_Basic

namespace NechitaRDM.MP

open MeasureTheory Filter Topology

/-- **Lemma 2, (45)** (p. 13). For Wishart matrices `Wₙ` of parameters `n` and `k(n)` with
`k(n)/n → c ∈ (0, ∞)`, the traces `Sₙ = Tr Wₙ` satisfy `Sₙ / (n k(n)) → 1` almost surely. -/
theorem lemma_2_eq_45 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (c : ℝ) (hc : 0 < c) (k : ℕ → ℕ)
    (hlim : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c))
    (X : (n : ℕ) → Ω → Matrix (Fin n) (Fin (k n)) ℂ)
    (hX : ∀ n, IsComplexGaussianMatrix P (X n)) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => (wishart (X n ω)).trace.re / ((n : ℝ) * (k n : ℝ))) atTop
      (𝓝 1) := by sorry

end NechitaRDM.MP
