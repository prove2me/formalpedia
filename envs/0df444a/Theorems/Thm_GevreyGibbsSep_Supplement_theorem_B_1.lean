-- Prove2me | Theorems.Thm_GevreyGibbsSep_Supplement_theorem_B_1
-- name    : GevreyGibbsSep.Supplement.theorem_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T10:03:04.598894+00:00
-- url     : https://prove2.me/theorems/1a8e1d98-0260-4039-a505-0ed62d5d99b6
-- title:
--   Theorem B.1 — Gevrey constants of $F=\log(1+(\alpha-1)\chi_{\nu,\ell})$: $|\partial^aF|\le\frac12(\|a\|_1!)^s(2\log^s\alpha/(r_s\nu))^{\|a\|_1}$
-- statement:
--   Let $s>1$, $\alpha\ge e$, $0<\ell<2\pi$ and $0<\nu\le\ell/4$, and let $\chi_{\nu,\ell}(x)=\prod_{k=1}^d H_\nu(x_k)H_\nu(\ell-x_k)$ be the mollified two-level profile on $\mathbb R^d$ (Definition B.5). Put
--   $$
--   F:=\log\big(1+(\alpha-1)\chi_{\nu,\ell}\big)\quad\text{on }\mathbb R^d .
--   $$
--
--   **Theorem B.1 (Gevrey constants of $F$).** For every multi-index $a=(a_1,\dots,a_d)\in\mathbb N^d\setminus\{0\}$ and every $x\in\mathbb R^d$,
--   $$
--   \big|\partial^aF(x)\big|\;\le\;\frac12\,\big(\|a\|_1!\big)^s\left(\frac{2\log^s\alpha}{r_s\,\nu}\right)^{\|a\|_1},
--   $$
--   where $\|a\|_1=a_1+\dots+a_d$ and $r_s:=\min\{r_1,\,Z_s/(e^2q_s)\}$ is the constant of (B38), with $t=1/(s-1)$, $r_1=\min\big\{\tfrac{1}{8(t+1)4^s},\tfrac{(t\,2^{-(t+1)})^{1/t}}{16(t+1)}\big\}$, $q_s=\max\{4,2^{t+2}t\}$ and $Z_s=\int_{-1}^1\psi_s$.
--
--   Since the scaled potential of the bump density equals $-F$ plus a constant on $[0,2\pi)^d$ (B36), this bound gives the Gevrey seminorm constants of the hard instances of the classical lower bound (Theorem B.2, Corollary 1).
--
--   **Formalization Note** $(\|a\|_1!)^s$ is the factorial of the total order, not $a!=\prod_i a_i!$; the power $s$ is real. $\chi_{\nu,\ell}$ and $r_s$ are the published definitions of the mission.
--
--   Differences from the source:
--
--   - encoding: F := log(1 + (α − 1)χ_{ν,ℓ}) (B36), χ_{ν,ℓ} of Definition B.5 with the section's 0 < ℓ < 2π, 0 < ν ≤ ℓ/4 and d ≥ 1 → fun y => Real.log (1 + (α - 1) * chi s ν ℓ y) with the published chi on ℝ^d, hypotheses 0 < ℓ < 2π, 0 < ν ≤ ℓ/4, 0 < d; reason: the section's standing assumptions on the bump parameters (Definition 4, p.13; Lemma B.6, p.43) made explicit; same function
--   - encoding: ∂^a, ‖a‖₁!, (·)^s, r_s of (B38) → published partialDeriv (fixed coordinate order), factorial of ∑ a_i cast to ℝ with real power s, published rs; reason: Lean conventions of the base mission; same values for the smooth F
-- source:
--   Olivucci, Sobchuk, Hoque, Hnybida, Kim, Shayeghi, Ronagh, Provable Quantum–Classical Separation for Continuous Gibbs Sampling, arXiv:2608.24527 (held version, sha256 d4fd40eb…), Theorem B.1, Eqs. (B36)–(B38), p.41

import Mathlib
import Definitions.Def_GevreyGibbsSep_partialDeriv
import Definitions.Def_GevreyGibbsSep_chi
import Definitions.Def_GevreyGibbsSep_rs

open MeasureTheory
open scoped ENNReal InnerProductSpace

namespace GevreyGibbsSep

namespace Supplement

/-- Theorem B.1 (Gevrey constants of `F`), arXiv:2608.24527 (held version, sha256 d4fd40eb…),
Eqs. (B36)–(B38), p.41. Let `α ≥ e` and `s > 1`, and let `F := log(1 + (α − 1) χ_{ν,ℓ})` on `ℝ^d`
(B36). Then for every `a ∈ ℕ^d \ {0}` and every `x ∈ ℝ^d`,
`|∂^a F(x)| ≤ ½ (‖a‖₁!)^s (2 log^s α/(r_s ν))^{‖a‖₁}`, with `r_s` of (B38).

**Formalization Note** `χ_{ν,ℓ}` is the published `chi` on all of `ℝ^d` (not periodized) and
`r_s` the published `rs`. The bump parameters satisfy the section's standing `0 < ℓ < 2π`,
`0 < ν ≤ ℓ/4` (Definition 4, p.13; Lemma B.6, p.43), and `d ≥ 1`. `‖a‖₁! ` is the factorial of the
total order `∑ a_i` (not `a! = ∏ a_i!`); `(·)^s` is a real power. -/
theorem theorem_B_1 {d : ℕ} (hd : 0 < d) (s α ν ℓ : ℝ) (hs : 1 < s) (hα : Real.exp 1 ≤ α)
    (hℓ : 0 < ℓ) (hℓ2 : ℓ < 2 * Real.pi) (hν : 0 < ν) (hνℓ : ν ≤ ℓ / 4) :
    ∀ a : Fin d → ℕ, a ≠ 0 → ∀ x : Fin d → ℝ,
      |partialDeriv a (fun y => Real.log (1 + (α - 1) * chi s ν ℓ y)) x|
        ≤ 1 / 2 * ((∑ i, a i).factorial : ℝ) ^ s
            * (2 * Real.log α ^ s / (rs s * ν)) ^ (∑ i, a i) := by sorry

end Supplement

end GevreyGibbsSep
