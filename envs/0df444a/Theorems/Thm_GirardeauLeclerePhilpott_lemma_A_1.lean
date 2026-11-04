-- Prove2me | Theorems.Thm_GirardeauLeclerePhilpott_lemma_A_1
-- name    : GirardeauLeclerePhilpott.lemma_A_1
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T00:18:48.177201+00:00
-- url     : https://prove2.me/theorems/7fbd0860-506b-49aa-ba74-55dd4065ca66
-- title:
--   Lemma A.1 (Girardeau–Leclère–Philpott) — vanishing gap with $f^k$ implies vanishing gap with $f^{k-1}$
-- statement:
--   This is Lemma A.1 of Girardeau–Leclère–Philpott, the technical lemma used in convergence proofs of SDDP-type cutting-plane methods to pass from one iteration's approximation to the previous one.
--
--   Let $X$ be a compact subset of a (pseudo)metric space, let $f:X\to\mathbb R$, and let $(f^k)_{k\in\mathbb N}$ be functions on $X$. Assume the following:
--
--   1. Each $f^k$ is $L$-Lipschitz on $X$ with a common constant $L$.
--   2. The sequence is monotone and bounded by $f$: $f^k(x)\le f^{k+1}(x)\le f(x)$ for all $k$ and all $x\in X$.
--
--   Then for every sequence $(x^k)$ in $X$,
--
--   $$
--   \lim_{k\to+\infty} f(x^k)-f^k(x^k)=0\quad\Longrightarrow\quad\lim_{k\to+\infty} f(x^{k})-f^{k-1}(x^{k})=0 .
--   $$
--
--   In SDDP-type convergence proofs this lemma transfers the vanishing of the gap $\mathcal Q_t-\mathcal Q^k_t$ at the trial points to the gap with the approximation $\mathcal Q^{k-1}_t$ of the previous iteration. It is used in (4.28) and (4.32) of Guigues' risk-averse analysis.
--
--   **Formalization Note** The original lemma assumes $f$ convex and states an equivalence. Only the nontrivial implication is stated here, and convexity of $f$ is dropped because it is not needed. The conclusion is written with the index shift $k\mapsto k+1$: $f(x^{k+1})-f^{k}(x^{k+1})\to0$.
-- source:
--   Girardeau, Leclère, Philpott, On the convergence of decomposition methods for multistage stochastic convex programs, Math. Oper. Res. 40(1):130-145, 2015, Appendix, Lemma A.1 (p. 143); https://leclere.github.io/files/papers/2015-SDDP.pdf

import Mathlib
open Filter Topology

namespace GirardeauLeclerePhilpott

theorem lemma_A_1 {E : Type*} [PseudoMetricSpace E] (X : Set E) (hX : IsCompact X)
    (f : E → ℝ) (F : ℕ → E → ℝ) (L : ℝ)
    (hL : ∀ k, ∀ x ∈ X, ∀ y ∈ X, |F k x - F k y| ≤ L * dist x y)
    (hmono : ∀ k, ∀ x ∈ X, F k x ≤ F (k + 1) x) (hle : ∀ k, ∀ x ∈ X, F k x ≤ f x)
    (x : ℕ → E) (hx : ∀ k, x k ∈ X)
    (h : Tendsto (fun k => f (x k) - F k (x k)) atTop (𝓝 0)) :
    Tendsto (fun k => f (x (k + 1)) - F k (x (k + 1))) atTop (𝓝 0) := by sorry

end GirardeauLeclerePhilpott
