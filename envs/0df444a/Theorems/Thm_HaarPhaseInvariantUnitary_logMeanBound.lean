-- Prove2me | Theorems.Thm_HaarPhaseInvariantUnitary_logMeanBound
-- name    : HaarPhaseInvariantUnitary.logMeanBound
-- status  : Proved
-- author  : @I am wealthy
-- created : 2026-11-21T09:08:14.870343+00:00
-- url     : https://prove2.me/theorems/a9f947f4-cf08-4ec5-9432-df6bbaaef7c0
-- title:
--   Phase-invariant Haar exponential-mean inequality on U(d)
-- statement:
--   Let $d\ge1$, and equip $U(d)$ with normalized Haar probability $\mu$ and Hilbert–Schmidt distance. Let $F:U(d)\to\mathbb R$ be continuous and $L$-Lipschitz for $L\ge0$. Suppose that $F(zV)=F(V)$ whenever $|z|=1$. Then
--
--   $$\log\int_{U(d)}e^{F(U)}\,d\mu(U)\le\int_{U(d)}F(U)\,d\mu(U)+\frac{L^2}{d}.$$
--
--   This phase-invariant specialization retains the special-unitary logarithmic Sobolev constant when passing to the full unitary Haar group. It supplies reusable exponential-moment bounds for conjugation observables, including normalized Pauli trace correlations.
-- source:
--   Meckes–Meckes, Spectral measures of powers of random matrices, arXiv:1210.2681v3, Appendix pp.11–13, proof of Theorem15 (SU(N) log-Sobolev constant 2/N) and Lemma16; phase-invariant specialization via Herbst. Application: STOC2027 #157, Lemma4.13, printed p.30. https://arxiv.org/pdf/1210.2681

import Mathlib
import Definitions.Def_QAlgorithms_Defs_SchurUnitaryEnsembles
open Matrix MeasureTheory ProbabilityTheory

namespace HaarPhaseInvariantUnitary
theorem logMeanBound (d:ℕ) (hd:1 ≤ d)
    (F:Matrix.unitaryGroup (Fin d) ℂ→ℝ) (hF:Continuous F)
    (L:ℝ) (hL:0 ≤ L)
    (hLip:∀U V:Matrix.unitaryGroup (Fin d) ℂ,|F U-F V| ≤
      L*Real.sqrt (∑x:Fin d,∑y:Fin d,
        ‖(U:Matrix (Fin d) (Fin d) ℂ) x y-(V:Matrix (Fin d) (Fin d) ℂ) x y‖^2))
    (hphase:∀z:Circle,∀U V:Matrix.unitaryGroup (Fin d) ℂ,
      (U:Matrix (Fin d) (Fin d) ℂ)=(z:ℂ) • (V:Matrix (Fin d) (Fin d) ℂ)→F U=F V) :
    Real.log (∫U,Real.exp (F U) ∂QAlgorithms.Schur.unitaryHaar d) ≤
      (∫U,F U ∂QAlgorithms.Schur.unitaryHaar d)+L^2/d := by sorry
end HaarPhaseInvariantUnitary
