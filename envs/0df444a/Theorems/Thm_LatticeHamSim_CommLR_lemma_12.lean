-- Prove2me | Theorems.Thm_LatticeHamSim_CommLR_lemma_12
-- name    : LatticeHamSim.CommLR.lemma_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:06:00.955788+00:00
-- url     : https://prove2.me/theorems/bff13cab-a443-4740-9f8e-b9f1e819893b
-- title:
--   Lemma 12, p. 21 — Lieb–Robinson commutator bound under (14)–(15)
-- statement:
--   Let $H=\sum_Zh_Z$ be a finite Hamiltonian with each $h_Z$ Hermitian and supported on $Z$. Suppose the terms satisfy (14) for $0<\eta\le1$ and the weighted exponential decay condition (15) for $\zeta,\mu>0$. Let $A$ be supported on $X$ and $B$ on a disjoint set $Y$. Then, for every real $t$,
--
--   $$\|[A(t),B]\|\le\frac{2}{\sqrt\eta}\|A\|\|B\|\bigl(e^{\zeta|t|\sqrt{8\eta}}-1\bigr)\sum_{x\in X}e^{-\mu\operatorname{dist}(x,Y)}.$$
--
--   The estimate quantifies the spatial suppression of the commutator and the velocity scale proportional to $\sqrt\eta$.
--
--   **Formalization Note** The source proof explicitly assumes $X\cap Y=\varnothing$ on page 24; without it the printed inequality fails at $t=0$. Positivity of $\eta$ is required because the paper's prefactor $2/\sqrt\eta$ is undefined at zero. A system satisfying (14) for $\eta=0$ also satisfies it for every $0<\eta\le1$. Operators are finite complex matrices with the L2 operator norm; the system is time independent. Point-to-empty distance is zero, but an operator supported on the empty set is scalar, so the commutator vanishes.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 21, Appendix C.1, Lemma 12 (16); disjointness used p. 24 after (31)

import Mathlib
import Definitions.Def_LatticeHamSim_CommLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.CommLR

/-- Lemma 12, with the disjoint-support and positive-eta repairs. -/
theorem lemma_12 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ]
    {q : ℕ} (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian)
    (hsupp : ∀ X, SupportedOn X (h X))
    (η ζ μ : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (h14 : ∀ X Y, ‖h X * h Y - h Y * h X‖ ≤
      2 * η * ‖h X‖ * ‖h Y‖)
    (hζ : 0 < ζ) (hμ : 0 < μ)
    (h15 : ∀ x : Λ,
      ∑ Z ∈ Finset.univ.filter (fun Z : Finset Λ => x ∈ Z),
        ‖h Z‖ * (Z.card : ℝ) ^ 2 *
          Real.exp (μ * Metric.diam (Z : Set Λ)) ≤ ζ)
    (X Y : Finset Λ) (hXY : Disjoint X Y)
    (A B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hA : SupportedOn X A) (hB : SupportedOn Y B) (t : ℝ) :
    ‖evolve (H h) t A * B - B * evolve (H h) t A‖ ≤
      2 / Real.sqrt η * ‖A‖ * ‖B‖ *
        (Real.exp (ζ * |t| * Real.sqrt (8 * η)) - 1) *
        ∑ x ∈ X, Real.exp (-(μ * Metric.infDist x (Y : Set Λ))) := by sorry

end LatticeHamSim.CommLR
