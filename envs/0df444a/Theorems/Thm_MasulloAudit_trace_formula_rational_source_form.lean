-- Prove2me | Theorems.Thm_MasulloAudit_trace_formula_rational_source_form
-- name    : MasulloAudit.trace_formula_rational_source_form
-- status  : Open
-- author  : @lll
-- created : 2026-11-21T00:47:17.129035+00:00
-- url     : https://prove2.me/theorems/349e4bbd-c20f-49b2-8bde-edec03c051a8
-- title:
--   Masullo's Theorem 12.5.1.1 for $\mathbf Q$ in source (adelic) form (equivalent to RH)
-- statement:
--   This is Masullo's Theorem 12.5.1.1 (*The Music of the Primes*, pp. 519–520) for $F=\mathbf Q$ and norm-invariant tests, stated in the **source's adelic form**, with genuine local integrals over $\mathbf R^\times$ and $\mathbf Q_p^\times$.
--
--   Let $\alpha>0$ and let $\varphi$ be an admissible test (`MasulloRH.IsRationalTraceTest`: smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$), viewed as $g\mapsto\varphi(|g|)$. For each prime $p$, choose any additive Haar measure $\mu_p$ on $\mathbf Q_p$ (multiplicative measure $d\mu_p/|g|_p$). The real-place integrand is integrable on $\mathbf R^\times$, each $p$-adic integrand is integrable, the family of prime-place terms is summable, the windowed zero family is summable, and
--
--   $$
--   \frac12\int_{\mathbf R^\times}\varphi(|x|)\frac{|x|^{1/2}}{|1-x|}\frac{dx}{|x|}+\sum_p\frac{\log p}{\mu_p(\mathbf Z_p^\times)}\int_{\mathbf Q_p^\times}\varphi(|g|_p)\frac{|g|_p^{1/2}}{|1-g|_p}\frac{d\mu_p(g)}{|g|_p}=\Phi(\tfrac12)+\Phi(-\tfrac12)-\sum_{|\operatorname{Re}\rho-\frac12|<\alpha}m_\rho\,\Phi(\rho-\tfrac12).
--   $$
--
--   Here $\Phi$ is the Mellin transform of $\varphi$, and the sum runs over the nontrivial zeros of $\zeta$ in the open window, with multiplicity.
--
--   **Status: open, and of RH strength. No proof is claimed here.** This node is the source-faithful counterpart of the formalization `MasulloRH.trace_formula_rational`, which is also open. By the proved `MasulloAudit.geometric_side_eq_formal_lhs`, the two left-hand sides agree. So this statement, which quantifies over all $\alpha>0$, is equivalent to the Riemann hypothesis (cf. `MasulloRH.trace_formula_rational_iff_RH`). For one fixed $\alpha\in(0,\tfrac12)$ it is equivalent to every nontrivial zero satisfying $|\operatorname{Re}\rho-\tfrac12|<\alpha$ (`MasulloAudit.trace_formula_rational_fixed_window_iff`), a zero-free strip that is also not known. In the draft, the global-to-S-local step of the proof (§12.3, p. 514) is an empty section with the footnote "Include section."
--
--   **Formalization Note.** Mathlib provides no measurable structure or Haar measure on $\mathbf Q_p$ at this revision, so these are parameters: families of `MeasurableSpace`/`BorelSpace` instances and Haar measures. A local instance supplies `Fact p.Prime` for `p : Nat.Primes`. The local integrands are textually those of `MasulloAudit.geometric_side_eq_formal_lhs`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1, eqs. (12.5.1.1)-(12.5.1.3), pp. 519-520; Definitions A.3.2.1-A.3.2.2.

import Definitions.Def_MasulloRH_RationalTrace
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false

open MeasureTheory Set
open scoped Topology

namespace MasulloAudit

open MasulloRH

/-- Each `p : Nat.Primes` gives the `Fact` needed to form `ℚ_[p]`. -/
local instance factPrimes (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-- Masullo, Theorem 12.5.1.1 (ζ case, `K = ℚ`), in its source form (12.5.1.1)–(12.5.1.3).
For every window `α > 0`, every norm-invariant test `φ(g) = ϕ(|g|_v)` with `ϕ` an admissible
rational trace test, and every family of Borel measurable structures and additive Haar measures
`μ_p` on the `ℚ_[p]`, with local multiplicative measures `μ_∞ = dx/|x|` on `ℝ^×` and
`μ_p = dμ_p/|g|_p` on `ℚ_p^×` (so `μ_p^×(ℤ_p^×) = μ_p {‖g‖ = 1}`):
the real-place and every `p`-adic local integral converge absolutely, the family of prime-place
terms is summable, the spectral family `zetaTraceTerm ϕ α` is summable, and

`½ ∫_{ℝ^×} φ |g|^{1/2}/|1-g| d^×g + Σ_p (log p / μ_p^×(ℤ_p^×)) ∫_{ℚ_p^×} φ |g|_p^{1/2}/|1-g|_p d^×g
  = M ϕ(1/2) + M ϕ(-1/2) - Σ_{ρ, |Re ρ - 1/2| < α} ord_ρ ζ · M ϕ(ρ - 1/2)`,

with the zero-sum convention of `MasulloRH.trace_formula_rational`. -/
theorem trace_formula_rational_source_form (α : ℝ) (hα : 0 < α) (φ : ℝ → ℂ)
    (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (zetaTraceTerm φ α) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      mellin φ (1 / 2) + mellin φ (-1 / 2) -
        ∑' ρ : ZetaZerosInTraceStrip α, zetaTraceTerm φ α ρ := by sorry

end MasulloAudit
