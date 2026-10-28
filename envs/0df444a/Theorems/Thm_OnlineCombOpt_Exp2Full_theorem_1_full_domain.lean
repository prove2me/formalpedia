-- Prove2me | Theorems.Thm_OnlineCombOpt_Exp2Full_theorem_1_full_domain
-- name    : OnlineCombOpt.Exp2Full.theorem_1_full_domain
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-28T00:36:01.803396+00:00
-- url     : https://prove2.me/theorems/12f45264-f329-4049-bd4d-b9217aa65b52
-- title:
--   Theorem 1 — full-domain EXP2 regret lower bound (corrected: excludes dimension one)
-- statement:
--   Let $n,d\in\mathbb N$ satisfy $n\ge d$ and $d\ne1$. There exist a finite nonempty action set $\mathcal A\subseteq\{0,1\}^d$ and a natural number $m$ such that every $a\in\mathcal A$ has $\sum_{i=1}^d a(i)=m$, and the following holds for every fixed real learning rate $\eta\ge0$.
--
--   Some deterministic oblivious loss sequence $z_t\in[0,1]^d$ forces the full-information EXP2 strategy, initialized uniformly on $\mathcal A$ and updated by Figure 2, to satisfy
--   $$
--   R_n(\mathcal A,\eta,z)
--   =\sum_{t=1}^n\sum_{a\in\mathcal A}p_t(a)a^\top z_t
--      -\min_{a\in\mathcal A}\sum_{t=1}^n a^\top z_t
--   \ge\frac1{100}d\sqrt d\sqrt n.
--   $$
--   The set $\mathcal A$ and its common weight $m$ are chosen before $\eta$; the loss sequence may depend on $\eta,n,d$. This witness implies the paper's lower bound on the supremum over admissible adversaries. The assertion retains every $d\ge2$, every $n\ge d$ including odd horizons, and $\eta=0$. At $d=0$ the singleton empty vector gives regret and bound zero, including when $n=0$.
--
--   This result records the limitation of treating each combinatorial action as an independent expert, uniformly over the choice of a fixed learning rate.
--
--   **Formalization Note** The imported probability recursion is the actual full-information update, without exploration mixing. The finite sum is the exact expected loss against the chosen deterministic sequence. The comparator minimum is outside the expectation in the source; determinism makes it the displayed finite minimum.
--
--   Differences from the source:
--   - correction: unrestricted dimension → $d\ne1$; reason: at $d=n=1$, every nonempty constant-weight binary action set is either $\{0\}$ or $\{1\}$, so every admissible loss process has regret zero while the claimed bound is $0.01$.
--   - generalization: supremum over admissible adversaries at least the threshold → a deterministic oblivious sequence attains the threshold; reason: a witness in this admissible subclass implies the source's supremum inequality, including attainment that the supremum alone does not assert.
--   - encoding: coordinates and rounds numbered from one → vectors indexed by Fin d and rounds indexed from zero; reason: index $t$ represents source round $t+1$, preserving the strictly earlier losses in each probability update.
--   - encoding: expected cumulative loss minus minimum expected comparator loss → finite probability-weighted loss minus a nonempty finite minimum for the deterministic witness; reason: these are exactly the source expectations for deterministic losses, with no integrability default or empty minimum.
--   - encoding: $0.01d^{3/2}\sqrt n$ → exact real $(1/100)d\sqrt d\sqrt n$; reason: natural dimensions are nonnegative, so the real expressions agree, with no natural division or floating-point approximation.
--   - encoding: losses specified for the first $n$ rounds → a sequence on all natural rounds with every coordinate in $[0,1]$; reason: every bounded finite sequence extends by zero beyond the horizon and regret uses only the first $n$ terms.
-- source:
--   Audibert, Bubeck, Lugosi, Regret in Online Combinatorial Optimization, arXiv:1204.4710v2, p. 6, Theorem 1 (proof in App. A, pp. 14–16)

import Mathlib
import Definitions.Def_OnlineCombOpt_Exp2LB_Setting

open Finset

open OnlineCombOpt.Exp2LB

namespace OnlineCombOpt.Exp2Full

/-- Theorem 1, corrected only by excluding dimension one (Audibert, Bubeck and Lugosi,
arXiv:1204.4710v2, p. 6; setting p. 2 and Figure 2 p. 7).
For every `n ≥ d` and `d ≠ 1`, one nonempty constant-weight binary action set works for every
fixed learning rate `η ≥ 0`. A deterministic oblivious bounded loss sequence attains the exact
lower bound `0.01 d^(3/2) √n`, strengthening the source's adversary-supremum conclusion.
The source fails at `d = n = 1`: every admissible action set is a singleton and has regret zero,
whereas the asserted bound is `0.01`. No divisibility, parity or positive-rate restriction is
imposed here. Dimension zero, including horizon zero, remains in the statement.
Indices are zero-based, and all losses after the horizon may be extended by zero. -/
theorem theorem_1_full_domain (n d : ℕ) (hnd : d ≤ n) (hd : d ≠ 1) :
    ∃ (A : Finset (Fin d → ℝ)) (m : ℕ), IsBinaryActionSet A m ∧
      ∀ η : ℝ, 0 ≤ η → ∃ z : ℕ → Fin d → ℝ,
        (∀ t i, z t i ∈ Set.Icc (0 : ℝ) 1) ∧
        (1 : ℝ) / 100 * d * Real.sqrt d * Real.sqrt n ≤ exp2Regret A η z n := by sorry

end OnlineCombOpt.Exp2Full
