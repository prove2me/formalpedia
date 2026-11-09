-- Prove2me | Theorems.Thm_IncoherentPurity_Adaptive_uniform_povm_moments
-- name    : IncoherentPurity.Adaptive.uniform_povm_moments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:57:55.947565+00:00
-- url     : https://prove2.me/theorems/a25f63c6-cfe0-4338-9dc0-8fdc05098456
-- title:
--   Lemma 2.4 — Moments of the uniform POVM
-- statement:
--   Apply the continuous uniform POVM to a $d\ge1$ state $\rho$. Its outcome $\psi$ has Born density $d\langle\psi|\rho|\psi\rangle$ relative to Haar pure states. For $X=(d+1)|\psi\rangle\langle\psi|-I$,
--
--   $$\mathbb EX=\rho,\quad\mathbb E[X^{\otimes2}]=\frac{(I^{\otimes2}+\rho\otimes I+I\otimes\rho)((d+1)\mathrm{SWAP}-I)}{d+2}.$$
--
--   The Born law is normalized and both moments are integrable. These are moments of the measurement outcome, rather than of an unweighted Haar sample.
--
--   Differences from the source:
--   - encoding: matrix, probability and asymptotic notation in the paper → finite matrix coordinates, explicit experiment measures, and universal real constants; reason: the representations retain every source instance and clause; finite-moment conclusions prevent default-zero integrals
--   - encoding: well-defined finite moments of the stated experiments → entrywise Integrable or MemLp 2 conclusions alongside the original moment or variance identities; reason: the experiments have bounded observations on the stated count domains; no additional hypothesis or source instance is imposed
-- source:
--   Lee–Wadhwa, Optimal Purity Estimation with Incoherent Measurements, STOC 2027 submission #66 (2026), pinned source.pdf; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/66.pdf; SHA-256 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce, Lemma 2.4, PDF p.9 = printed p.9

import Definitions.Def_IncoherentPurity_Adaptive_Estimators
import Definitions.Def_IncoherentPurity_Adaptive_Analytic

open MeasureTheory ProbabilityTheory Matrix
open scoped ENNReal ComplexOrder Matrix.Norms.Frobenius
set_option autoImplicit false
noncomputable section

namespace IncoherentPurity.Adaptive

/-- Lemma 2.4, PDF p.9, pinned source hash 7d80a6695c9c0b12bfa088a8f47d2a298b93f9fde9668867acfb4a95b19f03ce. -/
theorem uniform_povm_moments {d : ℕ} (hd : 0 < d) (H : HaarBasis d) (ρ : State d) :
  IsProbabilityMeasure (uniformLaw H ρ.val) ∧
  (∀ i j, Integrable (fun v => shadow v i j) (uniformLaw H ρ.val)) ∧
  (∀ i j, Integrable (fun v => tensorPower (shadow v) 2 i j) (uniformLaw H ρ.val)) ∧
  (Matrix.of fun i j => ∫ v, shadow v i j ∂uniformLaw H ρ.val) = ρ.val ∧
  (Matrix.of fun i j => ∫ v, tensorPower (shadow v) 2 i j ∂uniformLaw H ρ.val) =
    (1 / ((d : ℝ)+2)) •
      ((tensorPower (1 : Op d) 2 + tensorPair ρ.val 1 + tensorPair 1 ρ.val) *
       (((d : ℝ)+1) • permutationOp d 2 (Equiv.swap 0 1) - 1)) := by sorry

end IncoherentPurity.Adaptive
