-- Prove2me | Theorems.Thm_GaussAddit_Noise_eq_A1
-- name    : GaussAddit.Noise.eq_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-24T09:30:39.909409+00:00
-- url     : https://prove2.me/theorems/a0610b85-bf26-4867-86e6-e20dc46223c0
-- title:
--   Eq. (A1) — Weyl relation D†(μ⃗)D(ν⃗) = D(ν⃗ − μ⃗) exp((ν⃗·μ⃗† − μ⃗·ν⃗†)/2) for multi-mode displacements, in Fock coefficients
-- statement:
--   Let $m\ge0$ and $\vec\mu,\vec\nu\in\mathbb C^m$. The multi-mode displacements $D(\vec\mu)=\exp(\vec\mu\cdot\vec a^\dagger-\vec a\cdot\vec\mu^\dagger)$ satisfy
--   $$D^\dagger(\vec\mu)\,D(\vec\nu)=D(\vec\nu-\vec\mu)\,\exp\!\Big[\big(\vec\nu\cdot\vec\mu^\dagger-\vec\mu\cdot\vec\nu^\dagger\big)/2\Big],\qquad \vec\nu\cdot\vec\mu^\dagger=\sum_{r=1}^m\nu_r\overline{\mu_r}.$$
--   In Fock coefficients: for all $u,v\in\mathbb N^m$ the series $\sum_{w\in\mathbb N^m}\overline{\langle w|D(\vec\mu)|u\rangle}\,\langle w|D(\vec\nu)|v\rangle$ converges, and its sum is $\langle u|D(\vec\nu-\vec\mu)|v\rangle\,\exp[(\vec\nu\cdot\vec\mu^\dagger-\vec\mu\cdot\vec\nu^\dagger)/2]$.
--
--   This composition law of displacements is what reduces the operator $\Theta$ of (21) to a Gaussian integral in the proof of the paper's main identity.
--
--   **Formalization Note.** The identity is stated entrywise, with the matrix product written as a `HasSum` over the intermediate Fock index, so a divergent series cannot make it true.
--
--   Differences from the source:
--   - encoding: D_s†(μ⃗)D_s(ν⃗) on the s-th copy of H^{⊗m} → the same identity for the m-mode displacements of a single copy; reason: the copy index plays no role in the identity; every copy is the same m-mode space
--   - encoding: operator identity → identity of all Fock matrix elements, the product as a convergent sum over the intermediate index; reason: bounded operators on ℓ²(ℕ^m) are determined by their matrix elements
-- source:
--   Giovannetti & Lloyd, Additivity properties of a Gaussian channel, arXiv:quant-ph/0403075v3, p. 7, eq. (A1)

import Mathlib
import Definitions.Def_GaussAddit_Noise_Channel

open MeasureTheory
open scoped ENNReal InnerProductSpace Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsDensity rankOne)
open QAlgorithms.Papers.Independent.Dependency50.P39 (displacementMatrix)

namespace GaussAddit.Noise

theorem eq_A1 (m : ℕ) (μ ν : Fin m → ℂ) (u v : Occ m) :
    HasSum (fun w : Occ m => star (dispKernel μ w u) * dispKernel ν w v)
      (dispKernel (ν - μ) u v *
        Complex.exp ((∑ r, (ν r * star (μ r) - μ r * star (ν r))) / 2)) := by sorry

end GaussAddit.Noise
