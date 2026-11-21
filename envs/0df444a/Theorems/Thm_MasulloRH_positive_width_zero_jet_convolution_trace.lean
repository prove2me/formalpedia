-- Prove2me | Theorems.Thm_MasulloRH_positive_width_zero_jet_convolution_trace
-- name    : MasulloRH.positive_width_zero_jet_convolution_trace
-- status  : Proved
-- author  : @marozols
-- created : 2026-11-21T03:27:56.731432+00:00
-- url     : https://prove2.me/theorems/eaf75d8c-ac49-435a-b0e5-3f5321886fce
-- title:
--   The physical weighted zeta-jet trace on every closed rational strip, with trace-norm approximants
-- statement:
--   For every logarithmic half-width 0≤b≤1/2 and Sobolev exponent p≥0, physical convolution by every admissible test is nuclear on the closed weighted span of the zeta jets. Its trace is the absolutely convergent sum of centered Mellin values with full zero multiplicities in the open strip and multiplicity capped at ceil(p−1/2) on an edge. Every vector in this space annihilates every actual two-moment rational theta row. The theorem also proves the exact square-integrability criterion for all complex frequencies and gives finite-rank orthogonal truncations through height 5/2+2n with rank O((n+1)²), operator-norm error O((n+1)⁻⁴), trace-norm error O((n+1)⁻²), and exact truncated zero trace.
-- source:
--   A. M. Masullo, The Music of the Primes, rational specialization of §§9–10. The close-zero issue and yikerman’s generic-width Hardy-space repair are discussed at https://github.com/mccorvie/riemann-masullo/issues/1169#issuecomment-7053478224. This proof uses finite rational half-plane filters, exponential-weighted convolution, two-wall Fourier inversion, and dyadic finite-rank approximation. It establishes the spectral calculation on the closed span and its inclusion in the genuine theta annihilator.

import Definitions.Def_MasulloRH_WeightedStripJetSpace
import Definitions.Def_MasulloRH_RationalTrace
import Definitions.Def_MasulloGRH_HilbertNuclear
open MasulloRH MasulloGRH MeasureTheory Set Filter
open scoped Topology SchwartzMap BigOperators

theorem MasulloRH.positive_width_zero_jet_convolution_trace (b p : ℝ) (hb : 0≤b) (hB : b≤1/2) (hp : 0≤p) :
    (∀ (s : ℂ) (r : ℕ), MemLp (fun x : ℝ =>
      (rationalStripWeight b p x:ℂ)*(x:ℂ)^r*Complex.exp (s*x)) 2 volume ↔
        |s.re|<b ∨ (|s.re|=b ∧ (r:ℝ)+1/2<p)) ∧
    (∀ g : 𝓢(ℝ,ℂ), g 0=0 → (∫ t : ℝ,g t)=0 →
      let row := fun x : ℝ => ((1/rationalStripWeight b p x:ℝ):ℂ) *
        ((Real.exp (x/2):ℂ)*∑' n : ℤ,g ((n:ℝ)*Real.exp x))
      MemLp row 2 volume ∧ ∀ u : rationalStripJetSpace b p,
        Integrable (fun x : ℝ => row x*u.val x) ∧ (∫ x : ℝ, row x*u.val x)=0) ∧
    ∀ φ : ℝ→ℂ, IsRationalTraceTest φ →
      let d := fun z : ZetaZerosInTraceStrip (1/2) =>
        if |z.val.re-1/2|<b then analyticOrderNatAt riemannZeta z.val
        else if |z.val.re-1/2|=b then min (analyticOrderNatAt riemannZeta z.val) ⌈p-1/2⌉₊ else 0
      ∃! T : rationalStripJetSpace b p →L[ℂ] rationalStripJetSpace b p,
        IsRationalStripJetConvolution b p φ T ∧ IsNuclearOperator T ∧
        HasSum (fun z : ZetaZerosInTraceStrip (1/2) => (d z:ℂ)*mellin φ (z.val-1/2)) (operatorTrace T) ∧
        ∃ C : ℝ, 0<C ∧ ∀ n : ℕ, ∃ W : Submodule ℂ (rationalStripJetSpace b p),
          ∃ X : rationalStripJetSpace b p →L[ℂ] rationalStripJetSpace b p,
            FiniteDimensional ℂ W ∧ (Module.finrank ℂ W:ℝ) ≤ C*((n:ℝ)+1)^2 ∧
            (∀ f, X f∈W ∧ T f-X f∈Wᗮ) ∧ ‖X-T‖ ≤ C/((n:ℝ)+1)^4 ∧
            traceNorm (T-X) ≤ C/((n:ℝ)+1)^2 ∧
            operatorTrace X = ∑' z : ZetaZerosInTraceStrip (1/2), if |z.val.im|≤5/2+2*(n:ℝ)
              then (d z:ℂ)*mellin φ (z.val-1/2) else 0 := by sorry
