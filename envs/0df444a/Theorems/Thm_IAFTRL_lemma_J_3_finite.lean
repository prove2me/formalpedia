-- Prove2me | Theorems.Thm_IAFTRL_lemma_J_3_finite
-- name    : IAFTRL.lemma_J_3_finite
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-15T08:05:27.188299+00:00
-- url     : https://prove2.me/theorems/ddc14deb-1bbd-4718-8f5e-9e2ccea063ff
-- title:
--   Lemma J.3 (finite form) — a G-optimal law on a finite spanning list
-- statement:
--   This is the G-optimal design lemma (Kiefer–Wolfowitz) for a finite list of vectors, in the weight-vector form used by IA-FTRL.
--
--   Let $d\ge1$ and let $a_1,\dots,a_K\in\mathbb R^d$ span $\mathbb R^d$. For a probability vector $\pi=(\pi_1,\dots,\pi_K)$ write $\Sigma(\pi)=\sum_{j=1}^K\pi_j\,a_ja_j^\top$. Then there is a probability vector $\pi$ ($\pi_j\ge0$, $\sum_j\pi_j=1$) such that $\Sigma(\pi)\succ0$ and
--   $$
--   a_j^\top\,\Sigma(\pi)^{-1}a_j\le d\qquad\text{for every } j=1,\dots,K .
--   $$
--
--   Lemma D.10 of the source builds its feasible fallback from such a "G-optimal law", and the same law is the standard exploration distribution of linear-bandit algorithms. This statement supplies its existence for any finite spanning list.
--
--   **Formalization Note** The list need not be injective and need not lie in the unit ball (the paper states Lemma J.3 for any compact spanning set). The conclusion is `IsGOptLaw arms π`, whose matrix $\Sigma(\pi)$ is `BanditAlgorithm.linearAllocationMatrix arms π`.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits, arXiv:2611.01299, Lemma J.3, p.206 (finite action set; the law is the weight vector used in Lemma D.10, p.79)

import Mathlib
import Definitions.Def_IAFTRL_IsGOptLaw

namespace IAFTRL

open Matrix

/-- **Lemma J.3, finite form (G-optimal law on a finite spanning list).** Zhao–Tan,
*Best-of-Both-Worlds FTRL for Linear Bandits*, arXiv:2611.01299, Lemma J.3, p.206: "There is a
finite-support probability measure `π` such that `Σ(π) = ∫ aa^⊤ π(da) ≻ 0` and
`sup_{a∈𝒜} a^⊤Σ(π)^{-1}a ≤ d`."

For every list `a_1, …, a_K ∈ ℝ^d` (`d ≥ 1`) spanning `ℝ^d` there is a probability vector `π` on
the indices with `Σ(π) = Σ_j π_j a_j a_j^⊤ ≻ 0` and `a_j^⊤Σ(π)^{-1}a_j ≤ d` for every `j`.

**Formalization Note.** This is Lemma J.3 for the finite (hence compact) set `{a_1, …, a_K}`, with
the law written as the weight vector `IsGOptLaw` consumed by Lemma D.10. The list need not be
injective nor lie in the unit ball. -/
theorem lemma_J_3_finite {d K : ℕ} (hd : 1 ≤ d) (arms : Fin K → Fin d → ℝ)
    (hspan : Submodule.span ℝ (Set.range arms) = ⊤) :
    ∃ π : Fin K → ℝ, IsGOptLaw arms π := by sorry

end IAFTRL
