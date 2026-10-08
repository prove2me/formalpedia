-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_bilinear_parameter_saving
-- name    : OAI.TwoPointCorrelations.minor_arc_bilinear_parameter_saving
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:49.999286+00:00
-- url     : https://prove2.me/theorems/fde7c3d5-ef58-4453-8003-78bd4f59db92
-- title:
--   Minor-arc saving (log H / W)^{1/4} for bilinear prime windows
-- statement:
--   There are $C>0$ and $R_0\in\mathbb N$ such that the following holds. Let $P,J$ be finite sets of naturals and $X,H,N$ naturals with $1\le H\le X$, $\log H\ge1$, $J\subseteq\{1,\dots,N\}$, every $p\in P$ an odd prime with $\lfloor\log_2p\rfloor\in J$, and $R_0\le2^j\le X$ for $j\in J$. Let $W\ge1$ with $W\le2^j\le H/W$ for $j\in J$; $a,c:\mathbb N\to\mathbb C$ with $|a|\le1$ and $|c|\le1$ on $P$; $r\in\mathbb Z$ and $q\ge2$ with $W\le q\le H/W$; and $\alpha$ real with $\gcd(q,r)=1$ and $|\alpha-r/q|\le1/q^2$. Then
--
--   $$\sum_{k<X}\big|\texttt{minorArcBilinearWindow}\ P\ (X+H+1)\ H\ 1\ a\ c\ \alpha\ k\big|\le C\,X\,H\,(1+\log N)\Big(\frac{\log H}{W}\Big)^{1/4}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.minor_arc_bilinear_parameter_saving`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem minor_arc_bilinear_parameter_saving :
    ∃ C : ℝ, 0 < C ∧ ∃ R₀ : ℕ,
      ∀ (P J : Finset ℕ) (X H N : ℕ), 1 ≤ H → H ≤ X →
      1 ≤ Real.log (H : ℝ) → J ⊆ Icc 1 N →
      (∀ p ∈ P, Nat.log 2 p ∈ J) → (∀ p ∈ P, p.Prime ∧ p ≠ 2) →
      (∀ j ∈ J, R₀ ≤ 2 ^ j ∧ 2 ^ j ≤ X) →
      ∀ W : ℝ, 1 ≤ W →
      (∀ j ∈ J, W ≤ (2 : ℝ) ^ j ∧
        (2 : ℝ) ^ j ≤ (H : ℝ) / W) →
      ∀ (a c : ℕ → ℂ), (∀ m, ‖a m‖ ≤ 1) → (∀ p ∈ P, ‖c p‖ ≤ 1) →
      ∀ (r : ℤ) (q : ℕ), 2 ≤ q →
      W ≤ (q : ℝ) →
      (q : ℝ) ≤ (H : ℝ) / W →
      ∀ α : ℝ, IsCoprime (q : ℤ) r →
      |α - (r : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      (∑ k ∈ range X, ‖minorArcBilinearWindow P (X + H + 1) H 1 a c α k‖) ≤
        C * (X : ℝ) * H * (1 + Real.log (N : ℝ)) * (Real.log (H : ℝ)/W)^(1/4:ℝ) := by
  sorry

end OAI.TwoPointCorrelations
