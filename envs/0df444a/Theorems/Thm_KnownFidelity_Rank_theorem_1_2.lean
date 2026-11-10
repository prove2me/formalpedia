-- Prove2me | Theorems.Thm_KnownFidelity_Rank_theorem_1_2
-- name    : KnownFidelity.Rank.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:50:51.899218+00:00
-- url     : https://prove2.me/theorems/38f2db87-1c45-4784-a065-c71e8fcee59f
-- title:
--   Theorem 1.2 — $cq^2/(\varepsilon^2\log^4(q+1))\le\mathsf S(r,s,\varepsilon)\le Cq^2/\varepsilon^2$ with $q=\min\{r,s\}$
-- statement:
--   There are universal constants $c,C,\varepsilon_0>0$ and $q_0\in\mathbb N$ such that, with $q=\min\{r,s\}$, for all $q\ge q_0$ and $0<\varepsilon\le\varepsilon_0$,
--
--   $$\frac{c\,q^2}{\varepsilon^2\log^4(q+1)}\ \le\ \mathsf S(r,s,\varepsilon)\ \le\ \frac{C\,q^2}{\varepsilon^2}.$$
--
--   The lower bound holds for the reference $I_q/q$ and unknown states supported on $\mathbb C^q$:
--
--   $$\frac{c\,q^2}{\varepsilon^2\log^4(q+1)}\ \le\ \mathsf S^{(\le q)}_{I_q/q}(\varepsilon).$$
--
--   Here $\mathsf S(r,s,\varepsilon)$ is the worst case, over every ambient dimension and every known reference of rank at most $r$, of the number of copies needed to estimate the root fidelity $F(\rho,\sigma)$ within $\varepsilon$ with probability $2/3$ for every unknown state of rank at most $s$. So the copy complexity of fidelity estimation to a known state is quadratic in the smaller of the two ranks, up to logarithmic factors, independently of the ambient dimension. Logarithms are natural.
--
--   **Formalization Note** The copy complexities take values in $\mathbb N\cup\{\infty\}$ and the bounds are compared in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: least number of copies S → infimum in ℕ∞ (⊤ when no n works), compared via Nat.ceil cast to ℕ∞ or in ℝ≥0∞; reason: in ℕ the empty infimum is 0, which would make upper bounds trivial
--   - reading: The lower bound holds for the reference I_q/q and unknown states supported on ℂ^q → a third conjunct c q²/(ε² log⁴(q+1)) ≤ S^{(≤q)}_{I_q/q}(ε) with ambient dimension q; reason: the sentence is part of the theorem; on ℂ^q every state has rank at most q
-- source:
--   Lee, Jo, Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank, arXiv:2608.01770, Theorem 1.2, p. 2 (PDF p. 4)

import Mathlib
import Definitions.Def_KnownFidelity_Rank_worstCopyComplexity
import Definitions.Def_KnownFidelity_Rank_maxMixed

namespace KnownFidelity.Rank

/-- **Theorem 1.2 (Dependence on the smaller rank).**
Lee, Jo, *Fidelity Estimation to a Known Quantum State Is Nearly Quadratic in the Smaller Rank*,
arXiv:2608.01770, Theorem 1.2, printed p. 2 (PDF p. 4): "There are universal constants c, C, ε₀ > 0 and
q₀ ∈ N such that, with q = min{r, s}, for all q ≥ q₀ and 0 < ε ≤ ε₀,
cq²/(ε² log⁴(q + 1)) ≤ S(r, s, ε) ≤ Cq²/ε². (2) The lower bound holds for the reference I_q/q
and unknown states supported on C^q."

Three conclusions, for all `r, s` with `q = min{r, s} ≥ q₀` and all `0 < ε ≤ ε₀`:
(i) `c q²/(ε² log⁴(q+1)) ≤ S(r, s, ε)`;
(ii) `S(r, s, ε) ≤ C q²/ε²`;
(iii) `c q²/(ε² log⁴(q+1)) ≤ S^{(≤q)}_{I_q/q}(ε)` for the maximally mixed reference on `ℂ^q`
(ambient dimension `q`, every state on `ℂ^q`).

**Formalization Note.** `S(r, s, ε) = worstCopyComplexity r s ε` is the `ℕ∞` supremum over every
ambient dimension and every reference of rank at most `r` of the `ℕ∞` copy complexity (least `n`
such that one POVM on `n` copies succeeds with probability `2/3` on every state of rank at most
`s`). The bounds are compared in `ℝ≥0∞`. `c, C, ε₀, q₀` come before `r, s, ε`; `log` is natural.
Clause (iii) is the theorem's last sentence. -/
theorem theorem_1_2 :
    ∃ c C ε₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε₀ ∧ ∃ q₀ : ℕ, ∀ r s : ℕ, ∀ ε : ℝ,
      q₀ ≤ min r s → 0 < ε → ε ≤ ε₀ →
        ENNReal.ofReal (c * ((min r s : ℕ) : ℝ) ^ 2 /
            (ε ^ 2 * Real.log ((min r s : ℕ) + 1) ^ 4)) ≤ (worstCopyComplexity r s ε : ENNReal) ∧
        (worstCopyComplexity r s ε : ENNReal) ≤
          ENNReal.ofReal (C * ((min r s : ℕ) : ℝ) ^ 2 / ε ^ 2) ∧
        ENNReal.ofReal (c * ((min r s : ℕ) : ℝ) ^ 2 /
            (ε ^ 2 * Real.log ((min r s : ℕ) + 1) ^ 4)) ≤
          (copyComplexity (maxMixed (min r s)) (min r s) ε : ENNReal) := by sorry

end KnownFidelity.Rank
