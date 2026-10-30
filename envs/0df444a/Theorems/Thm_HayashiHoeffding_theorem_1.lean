-- Prove2me | Theorems.Thm_HayashiHoeffding_theorem_1
-- name    : HayashiHoeffding.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:19:24.520751+00:00
-- url     : https://prove2.me/theorems/0c22fb64-c521-46f9-9086-652960f13dec
-- title:
--   Theorem 1: $B(r|\rho\|\sigma)\ge\sup_{0\le s<1}\frac{-sr-\phi(s|\rho\|\sigma)}{1-s}$
-- statement:
--   Let $\rho$, $\sigma$ be density operators on an arbitrary complex Hilbert space $\mathcal H$ (possibly infinite-dimensional; $\rho$, $\sigma$ possibly singular and non-commuting), and let $r \in \mathbb R$. Let $B(r|\rho\|\sigma)$ be the optimal lower-limit exponent of the error probability of the first kind $\operatorname{Tr}\rho^{\otimes n}(I - T_n)$ over all test sequences whose error probability of the second kind $\operatorname{Tr}\sigma^{\otimes n}T_n$ has lower-limit exponent at least $r$, and let $\phi(s|\rho\|\sigma) = \log\operatorname{Tr}\rho^{1-s}\sigma^s$. Then
--
--   $$B(r|\rho\|\sigma) \;\ge\; \sup_{0 \le s < 1} \frac{-sr - \phi(s|\rho\|\sigma)}{1 - s} . \tag{3}$$
--
--   The inequality is in $[-\infty, +\infty]$; the right side is $+\infty$ when $\operatorname{Tr}\rho^{1-s}\sigma^s = 0$ for some $s$.
--
--   This is the direct part of the quantum Hoeffding bound: it shows that, under an exponential constraint $e^{-nr}$ on the second-kind error, the first-kind error can decay with the exponent on the right, which coincides with the classical Hoeffding exponent when $\rho$ and $\sigma$ commute. It was posed as an open problem by Ogawa and Hayashi.
--
--   **Formalization Note** $B$ is `hoeffdingB` (an `EReal` supremum over all test sequences on the completed tensor powers, copies indexed $k \mapsto k+1$, exponents as lower limits with $-\log 0 = +\infty$) and $\phi$ is `phi` (with $A^0$ the support projection). All arithmetic is in `EReal`.
--
--   Differences from the source:
--   - reading: the constraint printed as "$\lim_{n} \frac{-\log\operatorname{Tr}\sigma^{\otimes n}T_n \ge r}{n}$" → $\liminf_n \frac{-\log\operatorname{Tr}\sigma^{\otimes n}T_n}{n} \ge r$; reason: the only meaningful reading of the typesetting slip.
--   - reading: $\sup_{0 \le s \le 1}$ → $\sup_{0 \le s < 1}$; reason: at $s = 1$ the quotient divides by zero and is undefined on the page; any limiting value at $s = 1$ is a limit of values at $s < 1$, so the supremum is unchanged (in Lean $x/0 = 0$ would insert a junk value).
--   - reading: $\rho^1\sigma^0$ at $s = 0$ ($\sigma^0$ undefined on the page for singular $\sigma$) → $\rho\,\Pi_\sigma$ with $\Pi_\sigma$ the support projection; reason: the limit of $\sigma^s$ as $s \to 0^+$; the stronger reading (with $\sigma^0 = I$ the $s = 0$ term would be the void $-\log\operatorname{Tr}\rho = 0$).
--   - encoding: "Hilbert space", "density operators" → complex Hilbert space, positive trace-class operators of trace $1$; reason: the standard meaning of a density operator; no instance changes.
--   - encoding: $\mathcal H^{\otimes n}$, $\rho^{\otimes n}$ → completed Hilbert tensor powers indexed $k \mapsto k + 1$ ($n = k+1$), the $k$-th rate term divided by $k + 1$; reason: same spaces and sequences.
--   - encoding: $\log$, $\lim$ (underlined), $\sup$ → `elog` with $\log 0 = -\infty$, `liminf`, `sSup` in `EReal`; reason: the page's values, with $-\log 0 = +\infty$, in the extended reals.
--   - encoding: error probabilities and $\operatorname{Tr}\rho^{1-s}\sigma^s$ → real parts of `basisOperatorTrace`; reason: these traces are real.
-- source:
--   Hayashi, Error Exponent in Asymmetric Quantum Hypothesis Testing and Its Application to Classical-Quantum Channel coding, arXiv:quant-ph/0611013v2, Theorem 1, eq. (3), p.3

import Mathlib
import Definitions.Def_HayashiHoeffding_IsDensityOp
import Definitions.Def_HayashiHoeffding_phi
import Definitions.Def_HayashiHoeffding_hoeffdingB

namespace HayashiHoeffding

universe u

/-- **Theorem 1** (quantum Hoeffding lower bound). For density operators `ρ, σ` on any complex
Hilbert space and every real `r`,
`B(r|ρ‖σ) ≥ sup_{0 ≤ s < 1} (−sr − φ(s|ρ‖σ)) / (1 − s)`.

Hayashi, arXiv:quant-ph/0611013v2, Theorem 1, eq. (3), p.3.

**Formalization Note.**
1. `B(r|ρ‖σ)` is `hoeffdingB` (supremum over all test sequences, with `lim inf` exponents and
   copies indexed `k ↦ k + 1`); `φ` is `phi` (`EReal`-valued, `−∞` when the trace vanishes, and
   `A^0` the support projection).
2. The printed range `0 ≤ s ≤ 1` becomes `0 ≤ s < 1`: at `s = 1` the quotient divides by zero
   and is undefined on the page (in Lean `x / 0 = 0` would insert a junk value).
3. All arithmetic is in `EReal`; since `φ(s) < +∞`, `−sr − φ(s)` never meets `⊤ − ⊤`. -/
theorem theorem_1 {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (ρ σ : H →L[ℂ] H) (hρ : IsDensityOp ρ) (hσ : IsDensityOp σ) (r : ℝ) :
    (⨆ s ∈ Set.Ico (0 : ℝ) 1,
        (((-(s * r) : ℝ) : EReal) - phi ρ σ s) / (((1 - s : ℝ)) : EReal)) ≤
      hoeffdingB ρ σ r := by sorry

end HayashiHoeffding
