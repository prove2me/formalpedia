-- Prove2me | Theorems.Thm_MasulloAudit_geometric_side_eq_formal_lhs
-- name    : MasulloAudit.geometric_side_eq_formal_lhs
-- status  : Proved
-- author  : @deleted
-- created : 2026-11-21T00:38:02.734804+00:00
-- url     : https://prove2.me/theorems/4e64a65d-13c9-45ae-8f9c-8fe1fa614146
-- title:
--   Geometric side of Masullo's Theorem 12.5.1.1 for $\mathbf Q$ equals the formal left-hand side
-- statement:
--   Let $\varphi$ be an admissible test (`MasulloRH.IsRationalTraceTest`: smooth, compactly supported in $(0,\infty)$, $\varphi(1)=0$), regarded as the norm-invariant function $g\mapsto\varphi(|g|)$ on the idele class group of $\mathbf Q$. For each prime $p$ choose any additive Haar measure $\mu_p$ on $\mathbf Q_p$, with multiplicative Haar measure $d\mu_p/|g|_p$. Then the geometric side of Masullo's Theorem 12.5.1.1 for $F=\mathbf Q$,
--
--   $$
--   \frac12\int_{\mathbf R^\times}\varphi(|x|)\frac{|x|^{1/2}}{|1-x|}\frac{dx}{|x|}+\sum_{p}\frac{\log p}{\mu_p(\mathbf Z_p^\times)}\int_{\mathbf Q_p^\times}\varphi(|g|_p)\frac{|g|_p^{1/2}}{|1-g|_p}\frac{d\mu_p(g)}{|g|_p},
--   $$
--
--   converges absolutely: every local integral converges and only finitely many primes contribute. It equals
--
--   $$
--   \int_1^\infty\bigl(\varphi(t)+\varphi(t^{-1})\bigr)\frac{\sqrt t}{t^2-1}\,dt+\sum_{p}\sum_{k\ge1}\frac{\log p}{p^{k/2}}\bigl(\varphi(p^k)+\varphi(p^{-k})\bigr),
--   $$
--
--   the left-hand side of the formalization `MasulloRH.trace_formula_rational`.
--
--   So the left-hand side of the formal statement used by the RH-equivalence results (`MasulloRH.trace_formula_rational_iff_RH` and the fixed-window results) equals the source's geometric side, for every normalization of the Haar measures. It combines `MasulloAudit.real_place_term_eq_realTraceIntegral` and `MasulloAudit.prime_place_term_eq_primePowerTraceSum`.
--
--   **Formalization Note.** Mathlib provides no measurable structure or Haar measure on $\mathbf Q_p$ at this revision, so the statement takes families of `MeasurableSpace`/`BorelSpace` instances and Haar measures $\mu_p$ as parameters. A local instance supplies `Fact p.Prime` for `p : Nat.Primes`. The conclusion includes integrability of each local integrand, finiteness of the set of contributing primes, and summability.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, Theorem 12.5.1.1, eqs. (12.5.1.1)-(12.5.1.2), p. 519; Definitions A.3.2.1-A.3.2.2.

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

/-- Full geometric side of Masullo, Theorem 12.5.1.1 (ζ case, `K = ℚ`), for norm-invariant
tests `φ(g) = ϕ(|g|_v)` with `ϕ` an admissible rational trace test. For an arbitrary family of
Borel measurable structures and additive Haar measures `μ_p` on the `ℚ_[p]` (the multiplicative
Haar measure being `dμ_p/|x|_p`, so `μ_p^×(ℤ_p^×) = μ_p {‖g‖ = 1}`), every local term is an
absolutely convergent integral, only finitely many primes contribute, and

`½ ∫_{ℝ^×} φ |g|^{1/2}/|1-g| d^×g + Σ_p (log p / μ_p^×(ℤ_p^×)) ∫_{ℚ_p^×} φ |g|_p^{1/2}/|1-g|_p d^×g`

equals the formal left side `∫_{(1,∞)} realTraceIntegrand ϕ + Σ_{(p,k)} primePowerTraceTerm ϕ (p,k)`
of `MasulloRH.trace_formula_rational`, with both prime sums summable. -/
theorem geometric_side_eq_formal_lhs (φ : ℝ → ℂ) (hφ : IsRationalTraceTest φ)
    (inst : ∀ p : Nat.Primes, MeasurableSpace ℚ_[p])
    [hB : ∀ p : Nat.Primes, BorelSpace ℚ_[p]]
    (μ : ∀ p : Nat.Primes, Measure ℚ_[p]) [hμ : ∀ p : Nat.Primes, (μ p).IsAddHaarMeasure] :
    IntegrableOn (fun x : ℝ => φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ))
        {x : ℝ | x ≠ 0} ∧
    (∀ p : Nat.Primes,
      IntegrableOn (fun g : ℚ_[p] => φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ))
        {g : ℚ_[p] | g ≠ 0} (μ p)) ∧
    (Function.support (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p))).Finite ∧
    Summable (fun p : Nat.Primes =>
      ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
        ∫ g in {g : ℚ_[p] | g ≠ 0},
          φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p)) ∧
    Summable (primePowerTraceTerm φ) ∧
    (1/2 : ℂ) * (∫ x in {x : ℝ | x ≠ 0},
        φ |x| * ((|x| ^ (1/2 : ℝ) / |1 - x| * (1 / |x|) : ℝ) : ℂ)) +
      ∑' p : Nat.Primes,
        ((Real.log p / (μ p).real {g : ℚ_[p] | ‖g‖ = 1} : ℝ) : ℂ) *
          ∫ g in {g : ℚ_[p] | g ≠ 0},
            φ ‖g‖ * ((‖g‖ ^ (1/2 : ℝ) / ‖1 - g‖ * (1 / ‖g‖) : ℝ) : ℂ) ∂(μ p) =
      (∫ t in Ioi (1:ℝ), realTraceIntegrand φ t) +
        ∑' i : Nat.Primes × ℕ, primePowerTraceTerm φ i := by sorry

end MasulloAudit
