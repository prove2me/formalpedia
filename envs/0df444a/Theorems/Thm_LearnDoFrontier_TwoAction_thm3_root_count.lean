-- Prove2me | Theorems.Thm_LearnDoFrontier_TwoAction_thm3_root_count
-- name    : LearnDoFrontier.TwoAction.thm3_root_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T17:35:32.023689+00:00
-- url     : https://prove2.me/theorems/656da560-cae2-4529-975c-753a1063968c
-- title:
--   Proof of Theorem 3, EC p. 4 — z^(n+n̄) − δ⁻¹p⁻¹z^n̄ + p⁻¹(1−p) has exactly n̄ roots, with multiplicity, in the open unit disk
-- statement:
--   Let $n, \bar n$ be positive integers, $\delta \in (0,1)$ and $p \in (0,1)$, and consider the complex polynomial
--   $$f(z) = z^{n + \bar n} - \delta^{-1} p^{-1} z^{\bar n} + p^{-1}(1 - p).$$
--   Then $f$ has exactly $\bar n$ roots in the open unit disk $|z| < 1$, counted with multiplicity:
--   $$\sum_{z \in Z_{unit}(f)} m_z = \bar n,$$
--   where $Z_{unit}(f)$ is the set of distinct roots of $f$ with $|z| < 1$ and $m_z$ is the multiplicity of $z$.
--
--   With $p = p^A_\theta$, $n = n^A$, $\bar n = \bar n^A$ this is the root count for $f^A_\theta$ used in Theorem 3 and Theorem 6. With $p = 1 - p^B_\theta$, $n = \bar n^B$, $\bar n = n^B$ (note $(1-p)/p = p^B_\theta/(1-p^B_\theta)$) it gives the count $n^B$ for $f^B_\theta$. These counts make the matrices $Y$ of both theorems square.
--
--   **Formalization Note** The coefficients are real numbers coerced into $\mathbb C$; multiplicity is `Polynomial.rootMultiplicity`.
-- source:
--   Zhang, SSRN 3847049 (accepted version with E-Companion), EC p. 4 (PDF p. 47), proof of Theorem 3

import Mathlib
import Definitions.Def_LearnDoFrontier_TwoAction_Algebra
import Definitions.Def_LearnDoFrontier_TwoAction_Model

open Polynomial

namespace LearnDoFrontier.TwoAction

theorem thm3_root_count (n nbar : ℕ) (hn : 0 < n) (hnbar : 0 < nbar) (δ p : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (hp0 : 0 < p) (hp1 : p < 1) :
    let f : ℂ[X] := X ^ (n + nbar) - C ((δ⁻¹ * p⁻¹ : ℝ) : ℂ) * X ^ nbar + C ((p⁻¹ * (1 - p) : ℝ) : ℂ)
    ∑ z ∈ Zunit f, mult f z = nbar := by sorry

end LearnDoFrontier.TwoAction
