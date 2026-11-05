-- Prove2me | Theorems.Thm_FractionalSpectralGP_eq_4_3_chaos_basis
-- name    : FractionalSpectralGP.eq_4_3_chaos_basis
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:26:10.716233+00:00
-- url     : https://prove2.me/theorems/70889514-796a-4c73-acf6-a11d2e672f53
-- title:
--   §4, (4.3) — the $H_\alpha$ are an orthogonal base of $\mathcal W$ with $\|H_\alpha\|^2=\alpha!$
-- statement:
--   Let $P$ be the white noise measure, $f\mapsto\widetilde f$ the isometry of (4.2), and $(h_n)_{n\ge0}$ a real orthonormal basis of $L^2(\mathbb R,dx)$. For $\alpha\in\ell$ let $H_\alpha=\prod_k\mathbf h_{\alpha_k}(\widetilde{h_k})$, with $\mathbf h_j$ the Hermite polynomials. Then
--
--   1. every $H_\alpha$ is square-integrable;
--   2. $E[H_\alpha H_\beta]=0$ for $\alpha\ne\beta$;
--   3. $\|H_\alpha\|_{\mathcal W}^2=E[H_\alpha^2]=\alpha!$; and
--   4. the $H_\alpha$ span a dense subspace of $\mathcal W$: if $F\in L^2(P)$ satisfies $E[FH_\alpha]=0$ for all $\alpha$, then $F=0$.
--
--   This is the Wiener–Itô chaos decomposition in the coordinates used by the Kondratiev spaces; it also gives $\|F\|_{\mathcal H'_0}\le\|F\|_{\mathcal W}$, used in STEP 2 of Theorem 7.1.
--
--   Differences from the source:
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: orthogonal base of the real space 𝒲 → completeness tested against every complex F ∈ L²(P; ℂ); reason: a complex F is orthogonal to all real H_α iff its real and imaginary parts are
--   - encoding: multi-indices α = (α_1, α_2, …) with weight 2k at coordinate k → α : ℕ →₀ ℕ, coordinate n carries Z_n and weight 2(n + 1); reason: index shift k = n + 1; same objects
--   - encoding: orthogonal base with ‖H_α‖² = α! → L² membership, pairwise orthogonality, E[H_α²] = α!, and trivial orthogonal complement; reason: the definition of an orthogonal basis of a Hilbert space
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, §4, (4.3), p.10

import Mathlib
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_hermiteChaos
import Definitions.Def_FractionalSpectralGP_multiFactorial

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- §4, (4.3) (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, p.10): the functions `H_α = ∏_k h_{α_k}(h̃_k)`, `α ∈ ℓ`, form an
orthogonal base of the white noise space, and `‖H_α‖²_𝒲 = α!`.

**Formalization Note.** Four clauses: each `H_α` is in `L²(P)`; `E[H_α H_β] = 0` for `α ≠ β`;
`E[H_α²] = α!`; and an element of `L²(P; ℂ)` orthogonal to every `H_α` is `0` (so the closed span
is the whole space; complex `F` generalize the paper's real `𝒲`). `(h_n)` is any real orthonormal
basis of `L²(ℝ)` (the paper's Hermite functions are one). -/
theorem eq_4_3_chaos_basis (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) :
    (∀ α, MemLp (hermiteChaos P ι h α) 2 P) ∧
    (∀ α β, α ≠ β → ∫ ω, hermiteChaos P ι h α ω * hermiteChaos P ι h β ω ∂P = 0) ∧
    (∀ α, ∫ ω, hermiteChaos P ι h α ω ^ 2 ∂P = multiFactorial α) ∧
    ∀ F : Lp ℂ 2 P, (∀ α, ∫ ω, (F : Omega → ℂ) ω * (hermiteChaos P ι h α ω : ℂ) ∂P = 0) →
      F = 0 := by sorry

end FractionalSpectralGP
