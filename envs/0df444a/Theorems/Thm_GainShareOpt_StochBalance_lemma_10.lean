-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_10
-- name    : GainShareOpt.StochBalance.lemma_10
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:27.31262+00:00
-- url     : https://prove2.me/theorems/4216a297-236d-461c-b8fc-c36157e65922
-- title:
--   Lemma 10 — the constant extension (68) of an optimizer has $L=\gamma^*$
-- statement:
--   Let $(\gamma^*,f^*)$ be an optimal solution of Program (31) and $\tau^*=\tau(f^*)$. Its constant extension
--   $$\tilde f^*(z)=\begin{cases}f^*(z),&0\le z\le\tau^*,\\ 1-1/e,&z>\tau^*,\end{cases}\tag{68}$$
--   satisfies $L[\tilde f^*]=\gamma^*$, where $L$ is the value (6).
--
--   It gives the lower half $\Gamma(F_0)\ge\gamma^*$ of Theorem 6, and $\tilde f^*\in F_2$ is the attaining function of Theorem 3.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - encoding: an optimal solution (γ*, f*) chosen via Theorem 7 → any f with Feasible31 γ* f; reason: the lemma is stated for the chosen optimizer; Theorem 7 shows all optimizers agree on [0, τ*], so the extension does not depend on the choice
--   - reading: L[f̃*], the certificate functional of (1) → canonicalL, the value (6); reason: the page does not say which form of L is meant; its proof (p. 47) evaluates L[f̃*] through Proposition 4, which is stated for "the value of L[f] in (6)", and Theorem 1 identifies (6) with (44) on F0
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 47, Lemma 10, (68)

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical

namespace GainShareOpt.StochBalance

/-- Lemma 10: the constant extension (68) of an optimal `f*` beyond `τ(f*)` has value (6) equal
to `γ*`. -/
theorem lemma_10 (f : ℝ → ℝ) (hf : Feasible31 gammaStar f) :
    canonicalL (fun z => if z ≤ critTime f then f z else 1 - Real.exp (-1)) = gammaStar := by sorry

end GainShareOpt.StochBalance
