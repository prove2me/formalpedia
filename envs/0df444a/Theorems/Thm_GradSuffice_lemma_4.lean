-- Prove2me | Theorems.Thm_GradSuffice_lemma_4
-- name    : GradSuffice.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:19:50.493401+00:00
-- url     : https://prove2.me/theorems/d14909be-67b1-4ab5-936e-d4c9391deace
-- title:
--   Lemma 4, p.26 — a large martingale average yields a binary martingale shattering $W$ on average: (21) $\ge 9/16$
-- statement:
--   Let $X$ be a Banach space and let $W\subseteq B$ be a nonempty, symmetric, convex set (so $|x\cdot w|\le\|x\|_\star$ for $x\in X^\star$, $w\in W$).
--
--   **Lemma 4.** Suppose that for some constant $c>1-1/2^{25}$ and $M=2n$ there is a martingale $(\xi_1,\dots,\xi_M)$ in $X^\star$ with
--   $$\sqrt{\mathbb E\Big[\Big(\sup_{w\in W}\frac1M\sum_{i=1}^M\xi_i\cdot w\Big)^2\Big]}\ >\ c\,\sqrt{\sup_{i\le M}\mathbb E\big[\|\xi_i\|_\star^2\big]}.\tag{20}$$
--   Then there is a binary martingale $(\sigma_i\tilde\xi_i(\sigma_{<i}))_{i\le n}$ of size $n$ in $X^\star$ with
--   $$\mathbb E\Big[\sup_{w\in W}\frac1n\sum_{i=1}^n\mathbb 1\Big\{w\cdot\big(\sigma_i\tilde\xi_i(\sigma_{<i})\big)>\frac1{10}\|\tilde\xi_i(\sigma_{<i})\|_\star\Big\}\Big]\ \ge\ \frac9{16}.\tag{21}$$
--
--   Inequality (21) says that a uniformly random branch of the tree $\tilde\xi$ is realized by a single point of $W$ with margin $1/10$ (relative to the node norms) at more than half of its nodes on average; Proposition 1 then extracts a fully shattered subtree.
--
--   Differences from the source:
--   - reading: a martingale (size M = 2n, in X⋆) → a finitely supported martingale-difference law on (X⋆)^M; reason: §6.1 defines the paper's martingales as finitely supported
--   - encoding: binary martingale of size n in X∗ and E over it → an adaptive sequence ξ̃ with values in X⋆ multiplied by independent uniform signs; E is the average over the 2^n sign strings; reason: a binary martingale is exactly such a signed adaptive sequence
--   - encoding: sup over w ∈ W → sSup of the image of W, a nonempty bounded set of reals; reason: W ⊆ B is nonempty and |x · w| ≤ ‖x‖⋆
-- source:
--   Alon–Koren–Livni–Moran, When Do Gradients Suffice? A Characterization of First-Order Convex Optimization, manuscript of November 3, 2026 (STOC 2027 submission), Lemma 4, p.26, Eqs. (20)–(21)

import Mathlib
import Definitions.Def_NondualOpt_Tree
import Definitions.Def_NondualOpt_histPrefix
import Definitions.Def_NondualOpt_FinLaw
import Definitions.Def_GradSuffice_signR
import Definitions.Def_GradSuffice_IsMDSLaw
open Classical

namespace GradSuffice

/-- **Lemma 4 (from a large martingale average to average shattering).** Alon–Koren–Livni–Moran, *When Do Gradients Suffice?*, manuscript of November 3, 2026, Lemma 4, p.26: "Let
`W ⊆ B` be a nonempty, symmetric convex set. In particular, `|x · w| ≤ ‖x‖⋆` for `x ∈ X*` and `w ∈ W`.
Suppose that for some constant `c > 1 − 1/2^25` and `M = 2n` there exists a martingale such that
`√(E[(sup_{w∈W} (1/M) ∑_{i=1}^M ξᵢ · w)²]) > c √(sup_{i≤M} E[‖ξᵢ‖⋆²])` (20). Then there exists a binary
martingale of size `n` in `X*` such that
`E[sup_{w∈W} (1/n) ∑_{i=1}^n 𝟙{w · (σᵢ ξ̃ᵢ(σ<ᵢ)) > (1/10)‖ξ̃ᵢ‖⋆}] ≥ 9/16` (21)."

**Formalization Note.** The martingale is a finitely supported martingale-difference law `P` of
size `2n` in `X⋆` (`IsMDSLaw`); expectations are weighted sums over its support. A binary
martingale of size `n` is an adaptive sequence `ξ̃` (values in `X⋆`) multiplied by independent signs,
and `E` in (21) is the average over the `2^n` sign strings; `‖ξ̃ᵢ‖⋆` is the norm of `ξ̃ᵢ(σ<ᵢ)`. The
suprema over `W` are `sSup` of bounded nonempty sets of reals. -/
theorem lemma_4 (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] (W : Set X) (hW0 : W.Nonempty)
    (hWB : W ⊆ Metric.closedBall (0 : X) 1) (hWconv : Convex ℝ W) (hWsymm : ∀ w ∈ W, -w ∈ W)
    (c : ℝ) (hc : 1 - 1 / 2 ^ 25 < c) (n : ℕ)
    (P : NondualOpt.FinLaw (Set.univ : Set (Fin (2 * n) → StrongDual ℝ X))) (hP : IsMDSLaw P)
    (h20 : c * √(⨆ i : Fin (2 * n), ∑ x ∈ P.w.support, P.w x * ‖x i‖ ^ 2) <
      √(∑ x ∈ P.w.support,
        P.w x * sSup ((fun w => (1 / (2 * n : ℝ)) * ∑ i : Fin (2 * n), x i w) '' W) ^ 2)) :
    ∃ ξ : NondualOpt.Tree (StrongDual ℝ X) n,
      (9 / 16 : ℝ) ≤ (2 ^ n : ℝ)⁻¹ * ∑ σ : Fin n → Bool,
        sSup ((fun w => (1 / (n : ℝ)) * ∑ i : Fin n,
          (if (1 / 10 : ℝ) * ‖ξ i (NondualOpt.histPrefix σ i)‖ <
              signR (σ i) * ξ i (NondualOpt.histPrefix σ i) w then (1 : ℝ) else 0)) '' W) := by sorry

end GradSuffice
