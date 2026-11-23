-- Prove2me | Theorems.Thm_LeJEPAWorldModel_lejepa_linear_identifiability
-- name    : LeJEPAWorldModel.lejepa_linear_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:16:50.911801+00:00
-- url     : https://prove2.me/theorems/1313fadb-69a1-4eea-837f-85779f894aef
-- title:
--   Theorem 1: LeJEPA linear identifiability
-- statement:
--   Consider the Gaussian world with $0<\rho<1$. A positive pair is $z\sim\mathcal N(0,I_N)$ and $z'=\rho z+\sqrt{1-\rho^2}\,\eta$, with $\eta\sim\mathcal N(0,I_N)$ independent of $z$. Let $h:\mathbb R^N\to\mathbb R^N$ be measurable with $h(z)\sim\mathcal N(0,I_N)$, and let $\mathcal L(h)=\mathbb E\|h(z')-h(z)\|^2$. Then:
--
--   1. $\mathcal L(h)\ge2(1-\rho)N$;
--   2. equality holds if and only if there is an orthogonal $Q\in O(N)$ with $h(z)=Qz$ for $\gamma_N$-almost every $z$;
--   3. at any such optimum, $h(z')\mid h(z)\sim\mathcal N\big(\rho\,h(z),(1-\rho^2)I_N\big)$.
--
--   In words, any representation that satisfies both LeJEPA objectives recovers the latent variables up to a global rotation, together with their transition.
--
--   **Formalization Note** The identity $h(z)=Qz$ is between random variables, so it is stated $\gamma_N$-almost everywhere. Since $h(z)\sim\mathcal N(0,I_N)$, the conditional law in item 3 is equivalent to the statement that the pair $(h(z),h(z'))$ has the same joint law as $(z,z')$. The Lean statement uses this joint-law form.
-- source:
--   Klindt, LeCun and Balestriero, When Does LeJEPA Learn a World Model?, arXiv:2605.26379v2 (2026), Section 4.1, Theorem 1, eqs. (1)-(3), p. 5; proof in Appendix A, pp. 19-22

import Mathlib
import Definitions.Def_LeJEPAWorldModel_Basic

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace LeJEPAWorldModel

theorem lejepa_linear_identifiability (N : ℕ) (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (h : (Fin N → ℝ) → Fin N → ℝ) (hmeas : Measurable h)
    (hlaw : (stdGaussian N).map h = stdGaussian N) :
    2 * (1 - ρ) * N ≤ alignLoss N ρ h ∧
    (alignLoss N ρ h = 2 * (1 - ρ) * N ↔
      ∃ Q ∈ Matrix.orthogonalGroup (Fin N) ℝ, ∀ᵐ z ∂stdGaussian N, h z = Q.mulVec z) ∧
    (alignLoss N ρ h = 2 * (1 - ρ) * N →
      (ouPairLaw N ρ).map (fun p => (h p.1, h p.2)) = ouPairLaw N ρ) := by sorry

end LeJEPAWorldModel
