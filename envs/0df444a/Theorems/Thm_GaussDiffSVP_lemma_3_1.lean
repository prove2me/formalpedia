-- Prove2me | Theorems.Thm_GaussDiffSVP_lemma_3_1
-- name    : GaussDiffSVP.lemma_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T21:58:49.458277+00:00
-- url     : https://prove2.me/theorems/34d42592-c326-47b9-98a7-c471bca45ba4
-- title:
--   Lemma 3.1 — theta estimates $\rho_t(\Gamma+b) = (1\pm\varepsilon)t^n/\det\Gamma$ under smoothing
-- statement:
--   Let $\Gamma = B\mathbb Z^n$ be a full-rank lattice and $s>0$ with
--   $$\rho_{1/s}(\Gamma^*\setminus\{0\}) \le \varepsilon < 1,$$
--   where $\Gamma^* = \{y : \langle y,x\rangle\in\mathbb Z\ \forall x\in\Gamma\}$ and $\rho_t(S) = \sum_{x\in S}e^{-\pi\|x\|^2/t^2}$ (the smoothing condition $s\ge\eta_\varepsilon(\Gamma)$). Then:
--
--   1. for every $t\ge s$ and every shift $b\in\mathbb R^n$,
--   $$(1-\varepsilon)\frac{t^n}{\det\Gamma}\le\rho_t(\Gamma+b)\le(1+\varepsilon)\frac{t^n}{\det\Gamma};$$
--   2. for $\Gamma/t_0$ with a positive integer $t_0$, the same estimate holds at every parameter $t\ge s/t_0$;
--   3. for any lattice $K$, any $t>0$ and any $b$, $\rho_t(K+b)\le\rho_t(K)$.
--
--   These are the theta (Poisson summation) estimates used throughout the paper. The first clause is the Proved platform theorem `RegevLWE.GaussConv.claim_3_8` once $\varepsilon>0$.
--
--   Differences from the source:
--   - encoding: the sequence $\varepsilon_n<1$ of (11) → one number $0\le\varepsilon<1$; reason: the lemma is pointwise in $n$
--   - encoding: full-rank lattice $\Gamma$, $\det\Gamma$, $\Gamma/t_0$ → $\Gamma = B\mathbb Z^n$ with $\det B\ne0$, $\det\Gamma = |\det B|$, $\Gamma/t_0$ spanned by $t_0^{-1}B$; reason: every full-rank lattice has a basis
--   - generalization: any lattice $K$ (clause 3) → any $\mathbb Z$-submodule $K$ of $\mathbb R^n$; reason: a non-discrete subgroup has infinitely many points near $0$, so $\rho_t(K)=\infty$ and the inequality holds; lattices are the special case
--   - encoding: Gaussian masses $\rho_t(\cdot)$ → sums in $[0,\infty]$ (`SuperlatSVP.rhoSet`); reason: nonnegative sums; finite on lattice cosets
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Lemma 3.1, p.19 (setting (11), p.19)

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice

open SuperlatSVP
open scoped ENNReal

namespace GaussDiffSVP

/-- Lemma 3.1 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.19), in the setting (11): `Γ = Bℤⁿ` is a full-rank lattice and `s > 0` with
`ρ_{1/s}(Γ*∖{0}) ≤ ε < 1`, where `Γ* = {y : ⟨y, x⟩ ∈ ℤ ∀ x ∈ Γ}`. Then:

1. for every `t ≥ s` and every shift `b ∈ ℝⁿ`,
   `(1 − ε) tⁿ/det Γ ≤ ρ_t(Γ + b) ≤ (1 + ε) tⁿ/det Γ` (12);
2. for `Γ/t₀`, with positive integer `t₀`, the same estimate holds at parameters `t ≥ s/t₀`;
3. for any lattice `K`, any `t > 0` and any `b`, `ρ_t(K + b) ≤ ρ_t(K)`.

The first clause is the Proved platform theorem `RegevLWE.GaussConv.claim_3_8` (370102ae) after
(11) ⇒ `η_ε(Γ) ≤ s`, for `ε > 0`.

**Formalization Note.** `ρ_t(S) = ∑_{x ∈ S} e^{−π‖x‖²/t²}` is `SuperlatSVP.rhoSet` (a sum in
`ℝ≥0∞`); `Γ + b` is `{x : x − b ∈ Γ}`; `det Γ = |det B|`; `Γ/t₀` is the lattice of the basis
`t₀⁻¹B`. The paper's `ε_n` is a number here. In clause 3 `K` is any `ℤ`-submodule of `ℝⁿ`. -/
theorem lemma_3_1 {n : ℕ} (B : Matrix (Fin n) (Fin n) ℝ) (hB : B.det ≠ 0) (s ε : ℝ)
    (hs : 0 < s) (hε0 : 0 ≤ ε) (hε1 : ε < 1)
    (h11 : rhoSet (1 / s) {y | y ∈ RegevLWE.GaussConv.dual (lat B) ∧ y ≠ 0} ≤ ENNReal.ofReal ε) :
    (∀ t : ℝ, s ≤ t → ∀ b : E n,
      ENNReal.ofReal ((1 - ε) * t ^ n / |B.det|) ≤ rhoSet t {x | x - b ∈ lat B} ∧
        rhoSet t {x | x - b ∈ lat B} ≤ ENNReal.ofReal ((1 + ε) * t ^ n / |B.det|)) ∧
    (∀ t₀ : ℕ, 0 < t₀ → ∀ t : ℝ, s / t₀ ≤ t → ∀ b : E n,
      ENNReal.ofReal ((1 - ε) * t ^ n / |((t₀ : ℝ)⁻¹ • B).det|) ≤
          rhoSet t {x | x - b ∈ lat ((t₀ : ℝ)⁻¹ • B)} ∧
        rhoSet t {x | x - b ∈ lat ((t₀ : ℝ)⁻¹ • B)} ≤
          ENNReal.ofReal ((1 + ε) * t ^ n / |((t₀ : ℝ)⁻¹ • B).det|)) ∧
    (∀ K : Submodule ℤ (E n), ∀ t : ℝ, 0 < t → ∀ b : E n,
      rhoSet t {x | x - b ∈ K} ≤ rhoSet t (K : Set (E n))) := by sorry

end GaussDiffSVP
