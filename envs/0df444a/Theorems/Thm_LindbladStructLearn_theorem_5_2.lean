-- Prove2me | Theorems.Thm_LindbladStructLearn_theorem_5_2
-- name    : LindbladStructLearn.theorem_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T22:03:34.905353+00:00
-- url     : https://prove2.me/theorems/f9081e67-edd7-4031-9ac4-d9f2116358e6
-- title:
--   Theorem 5.2 — the simplified Algorithm 4 finds $\widehat\lambda$ with $\|\widehat\lambda - \lambda\|_{B_1} \le \varepsilon$
-- statement:
--   Let $1 < k \le n$, $g > 0$ and $0 < \varepsilon < g$ (the standing assumptions of Section 5, p.32). Let $\lambda$ be the coefficient vector of a $k$-local Lindbladian $\mathcal L_{\alpha,D}$ with $\|\mathcal L\|_{B_1} \le g$, and let $d \ge 1$ be a natural number with $\deg_{\varepsilon/(100\cdot16^k)}(\mathcal L) \le d$. Let $t, \eta > 0$ with
--
--   $$t < \frac{1}{200\cdot4^k\cdot(23k)!\,g}, \qquad \eta < \frac{\varepsilon}{96000\cdot256^k d}.$$
--
--   Suppose the estimates $\widehat{\mathcal F}_j$ used in round $j$ satisfy $\|\mathcal F(x^{(j)}) - \widehat{\mathcal F}_j(x^{(j)})\|_\infty \le \eta$ at the iterates $x^{(j)}$, $j < T = \lceil\log_2(g/\varepsilon)\rceil$. Then the output $\widehat\lambda = x^{(T)}$ of the simplified Algorithm 4 satisfies
--
--   $$\|\widehat\lambda - \lambda\|_{B_1} \le \varepsilon,$$
--
--   and in particular $\|\widehat\alpha - \alpha\|_\infty \le \varepsilon$ and $\|\widehat D - D\|_\infty \le \varepsilon$ (every coefficient is within $\varepsilon$).
--
--   This is the correctness of the iteration: accurate enough estimates of $\mathcal F$ at the iterates suffice to learn the structure and the coefficients.
--
--   Differences from the source:
--   - reading: d = deg_{ε/(100·16^k)}(L), the approximate degree → any natural d ≥ 1 with deg_{ε/(100·16^k)}(L) ≤ d; reason: the thresholds ε_j/(4d) and the bound on η divide by d, so the printed statement needs d ≥ 1; Theorem 1.1 uses the algorithm with any upper bound d
--   - generalization: estimates F̂(x) for given inputs x with ‖F(x) − F̂(x)‖_∞ ≤ η → round-dependent estimates F̂_j, accurate only at the iterates x^(j), j < T; reason: the proof evaluates F̂ only at the iterates, and the full algorithm's estimates are random and fresh per round; the printed hypothesis is the special case F̂_j = F̂
--   - encoding: λ̂ = (α̂, D̂), ‖α̂ − α‖_∞ ≤ ε and ‖D̂ − D‖_∞ ≤ ε → the iterate extended by zero, and every entry within ε of λ; reason: coefficient vectors on all pairs with λ(I,·) = 0
--   - encoding: A⁻¹ in (5.10) → Mathlib's matrix inverse of A_k; reason: A_k is invertible (Corollary 3.7)
-- source:
--   Lewis–Tang–Wright, Learning the structure of open quantum systems, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), Theorem 5.2, Eqs. (5.14)–(5.15), p.35; Algorithm 4, p.34

import Mathlib
import Definitions.Def_LindbladTolerant_Testing_lindblad_model
import Definitions.Def_LindbladStructLearn_alg4Iter
import Definitions.Def_LindbladStructLearn_Fvec
import Definitions.Def_LindbladStructLearn_toIdx
import Definitions.Def_LindbladStructLearn_ext
import Definitions.Def_LindbladStructLearn_b1Norm
import Definitions.Def_LindbladStructLearn_IsLindbladParams
import Definitions.Def_LindbladStructLearn_IsKLocal
import Definitions.Def_LindbladStructLearn_ApproxDegLe

set_option autoImplicit false
open scoped ComplexOrder BigOperators Matrix ENNReal NNReal

namespace LindbladStructLearn

open LindbladTolerant.Testing

/-- Theorem 5.2 (Lewis–Tang–Wright, *Learning the structure of open quantum systems*, arXiv:2606.30358 (held version, sha256 0af12079…2eb52e), p.35; Algorithm 4, "Simplified Algorithm", p.34): let `ε > 0` and let
`L = L_(α,D)` be a `k`-local Lindbladian with `‖L‖_B1 ≤ g` and `d = deg_(ε/(100·16^k))(L)`. Let
`t, η > 0` with `t < 1/(200 · 4^k · (23k)! g)` and `η < ε/(96000 · 256^k d)`. If the estimates
satisfy `‖F(x) − F̂(x)‖_∞ ≤ η`, then the simplified Algorithm 4 finds `λ̂ = (α̂, D̂)` with
`‖λ̂ − λ‖_B1 ≤ ε`; this also gives `‖α̂ − α‖_∞ ≤ ε` and `‖D̂ − D‖_∞ ≤ ε`.

**Formalization Note** The iteration is `alg4Iter` with `T = ⌈log₂(g/ε)⌉`. `d` is any natural number
`≥ 1` with `deg_(ε/(100·16^k))(L) ≤ d`. The estimates may depend on the round, `F̂ j`, and need to
be `η`-accurate only at the iterates `x^(j)`, `j < T`. Section 5's standing assumptions `k > 1`,
`g > 0`, `ε < g` (p.32) and `k ≤ n` (Notation 3.2) are hypotheses. -/
theorem theorem_5_2 (n k : ℕ) (hk : 1 < k) (hkn : k ≤ n) (g ε : ℝ) (hg : 0 < g) (hε : 0 < ε)
    (hεg : ε < g) (lam : Pauli n × Pauli n → ℂ) (hlam : IsLindbladParams lam)
    (hloc : IsKLocal k lam) (hB1 : b1Norm lam ≤ g) (d : ℕ) (hd : 1 ≤ d)
    (hdeg : ApproxDegLe (ε / (100 * 16 ^ k)) lam d) (t η : ℝ) (ht : 0 < t)
    (ht' : t < 1 / (200 * 4 ^ k * ((23 * k).factorial : ℝ) * g)) (hη : 0 < η)
    (hη' : η < ε / (96000 * 256 ^ k * d)) (Fhat : ℕ → (Idx n k → ℂ) → (Idx n k → ℂ))
    (hF : ∀ j < ⌈Real.logb 2 (g / ε)⌉₊,
      ‖Fvec t (toIdx lam) (alg4Iter n k d g Fhat j) - Fhat j (alg4Iter n k d g Fhat j)‖ ≤ η) :
    b1Norm (ext (alg4Iter n k d g Fhat ⌈Real.logb 2 (g / ε)⌉₊) - lam) ≤ ε ∧
      ∀ Q : Pauli n × Pauli n,
        ‖ext (alg4Iter n k d g Fhat ⌈Real.logb 2 (g / ε)⌉₊) Q - lam Q‖ ≤ ε := by sorry

end LindbladStructLearn
