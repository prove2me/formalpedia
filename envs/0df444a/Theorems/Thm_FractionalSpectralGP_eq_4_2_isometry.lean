-- Prove2me | Theorems.Thm_FractionalSpectralGP_eq_4_2_isometry
-- name    : FractionalSpectralGP.eq_4_2_isometry
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:08.918828+00:00
-- url     : https://prove2.me/theorems/2e4c6ace-4f63-4b66-92ab-63887d224d2e
-- title:
--   §4, (4.1)–(4.2) — $s\mapsto\widetilde s$ extends to a unique isometry $L^2(\mathbb R,dx)\to\mathcal W$
-- statement:
--   Let $P$ be the white noise measure on $\Omega=\mathcal S'$, i.e. $\int e^{-i\langle s',s\rangle}dP(s')=e^{-\|s\|^2/2}$ for $s\in\mathcal S$. For a real Schwartz function $s$ put $\widetilde s(\omega)=\langle\omega,s\rangle$. Then there is exactly one linear isometry
--
--   $$
--   \iota:L^2(\mathbb R,dx)\to L^2(\Omega,P)\qquad\text{with}\qquad\iota(s)=\widetilde s\ \ P\text{-a.e. for every }s\in\mathcal S .
--   $$
--
--   This is the isometry $f\mapsto\widetilde f$ through which $Z_n=\widetilde{h_n}$ and $X_\sigma(t)=\widetilde{Q_\sigma1_{[0,t]}}$ are defined.
--
--   Differences from the source:
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, Borel σ-algebra of 𝒮' → P a parameter satisfying (4.1), evaluation (cylinder) σ-algebra; reason: Minlos is not in Mathlib and (4.1) determines P; for 𝒮' the cylinder and Borel σ-algebras coincide
--   - reading: the isometry extends to all of L²(ℝ, dx) and is denoted by the same symbol → existence and uniqueness of the extension; reason: "the extension" presupposes uniqueness, which holds because 𝒮 is dense
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, (4.1)–(4.2), p.10

import Mathlib
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- §4, (4.1)–(4.2) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.10): for the white noise measure `P`, the map `s ↦ s̃`,
`s̃(ω) = ⟨ω, s⟩`, is an isometry from `𝒮` with the `L²(ℝ, dx)` norm into `𝒲`, and it extends to
all of `L²(ℝ, dx)`; the extension is unique.

**Formalization Note.** Stated as: there is exactly one complex-linear isometry
`ι : L²(ℝ; ℂ) → L²(P; ℂ)` with `ι(s) = ⟨·, s⟩` `P`-a.e. for every real Schwartz function `s`
(`IsWienerIsometry`). Complex scalars generalize the paper's real `𝒲`. -/
theorem eq_4_2_isometry (P : Measure Omega) (hP : IsWhiteNoise P) :
    ∃! ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P, IsWienerIsometry P ι := by sorry

end FractionalSpectralGP
