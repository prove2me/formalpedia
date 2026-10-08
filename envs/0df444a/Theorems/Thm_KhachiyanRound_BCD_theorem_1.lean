-- Prove2me | Theorems.Thm_KhachiyanRound_BCD_theorem_1
-- name    : KhachiyanRound.BCD.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:15:38.929739+00:00
-- url     : https://prove2.me/theorems/b3f131ff-5d47-4a01-9252-1dd52fc12f0e
-- title:
--   Theorem 1, p. 314 — for centrally symmetric 𝒜 the BCD finds a √((1 + ε)n)-rounding in O(n(ε⁻¹ + ln n + ln ln m)) iterations
-- statement:
--   There is a universal constant $C > 0$ with the following property. Let $n \ge 2$, let $\mathcal A = \{a_1,\dots,a_m\} \subset \mathbb{R}^n$ be centrally symmetric and full-dimensional, let $\varepsilon > 0$, and let $p_0, p_1, \dots$ be any run of the BCD method. Then there is an iterate $p_k$ with
--   $$k \le C\,n\big(\varepsilon^{-1} + \ln n + \ln\ln m\big)$$
--   such that $A(p_k)$ is positive definite and the ellipsoid $E_{p_k} = \{x \mid x^{\mathsf T}A(p_k)^{-1}x \le 1\}$ satisfies
--   $$E_{p_k} \subseteq \operatorname{conv}(\mathcal A) \subseteq \sqrt{(1+\varepsilon)n}\;E_{p_k},$$
--   i.e. $\sqrt{(1+\varepsilon)n}\,E_{p_k}$ is a $\sqrt{(1+\varepsilon)n}$-rounding ellipsoid for $\mathcal A$.
--
--   This is the centrally symmetric case of the paper's main result; the general case (Theorem 2) is reduced to it by a lift to $\mathbb{R}^{n+1}$.
--
--   **Formalization Note** The page counts $N(\varepsilon) = O(mn^2(\varepsilon^{-1} + \ln n + \ln\ln m))$ arithmetic operations: iterations times $O(nm)$ per iteration (the rank-one correction) plus $O(mn^2)$ to form $A_0^{-1}$. The Lean statement bounds the number of iterations instead; the operation count is not formalized. The constant $C$ is quantified before every instance datum. Full dimension (2.2) and $n \ge 2$ are the standing assumptions of §2 (p. 309), which the theorem's sentence does not repeat.
-- source:
--   Khachiyan, Rounding of polytopes in the real number model of computation, Math. Oper. Res. 21 (1996), p. 314, Theorem 1

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting

open scoped Pointwise

namespace KhachiyanRound.BCD

theorem theorem_1 :
    ∃ C : ℝ, 0 < C ∧ ∀ (n m : ℕ) (a : Fin m → Fin n → ℝ), 2 ≤ n → IsCentrallySymmetric a →
      affineSpan ℝ (Set.range a) = ⊤ → ∀ ε : ℝ, 0 < ε → ∀ p : ℕ → Fin m → ℝ, IsBCDRun a p →
        ∃ k : ℕ, (k : ℝ) ≤ C * n * (1 / ε + Real.log n + Real.log (Real.log m)) ∧
          (momentMatrix a (p k)).PosDef ∧
          LinearOptimization.ellipsoid 0 (momentMatrix a (p k)) ⊆ convexHull ℝ (Set.range a) ∧
          convexHull ℝ (Set.range a) ⊆
            Real.sqrt ((1 + ε) * n) • LinearOptimization.ellipsoid 0 (momentMatrix a (p k)) := by sorry
end KhachiyanRound.BCD
