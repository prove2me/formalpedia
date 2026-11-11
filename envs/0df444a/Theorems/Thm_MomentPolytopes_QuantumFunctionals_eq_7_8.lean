-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_eq_7_8
-- name    : MomentPolytopes.QuantumFunctionals.eq_7_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:02:26.39527+00:00
-- url     : https://prove2.me/theorems/37220c81-4d4d-4487-9a02-3f7321d9fca3
-- title:
--   §7.2, Eq. (7.8) — data-processing inequality D(A‖B) ≥ D(Λ(A)‖Λ(B)) for PSD A, B and CPTP Λ
-- statement:
--   Let $A,B$ be positive-semidefinite $n\times n$ complex matrices (of arbitrary traces, possibly singular), and let $\Lambda$ be a completely positive trace-preserving linear map from $n\times n$ to $n'\times n'$ complex matrices. With the quantum relative entropy $D(A\|B)=\operatorname{tr}[A\log A]-\operatorname{tr}[A\log B]$ if $\operatorname{im}A\subseteq\operatorname{im}B$ and $D(A\|B)=\infty$ otherwise,
--   $$D(A\|B)\ \ge\ D(\Lambda(A)\|\Lambda(B)).$$
--
--   The paper cites this monotonicity from [Wat18, Thm. 5.35] and applies it to the partial trace in the proof of Theorem 7.5, to matrices that need not have trace one.
--
--   Differences from the source:
--   - encoding: D valued in ℝ ∪ {∞}; traces taken on the images (fn. 43) → relEntropy in EReal with ∞ = ⊤; log is cfc Real.log, 0 on the kernel; reason: same values
--   - encoding: completely positive trace-preserving map between finite-dimensional matrix spaces → ℂ-linear Λ : Matrix m m ℂ → Matrix m' m' ℂ for finite index types m, m', trace preserving, with Λ ⊗ id_k positive for every k ∈ ℕ; reason: standard definition of complete positivity; same maps
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 56, eq. (7.8) (cited from [Wat18, Thm. 5.35])

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_RelativeEntropy

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Data-processing inequality, §7.2, eq. (7.8), p. 56 (cited from [Wat18, Thm. 5.35]):
`D(A‖B) ≥ D(Λ(A)‖Λ(B))` for all positive-semidefinite `A`, `B` (any traces, possibly singular)
and every completely positive trace-preserving map `Λ` between finite-dimensional matrix
spaces. -/
theorem eq_7_8 {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    (Λ : Matrix m m ℂ →ₗ[ℂ] Matrix m' m' ℂ) (hΛ : IsCPTP Λ)
    (A B : Matrix m m ℂ) (hA : A.PosSemidef) (hB : B.PosSemidef) :
    relEntropy (Λ A) (Λ B) ≤ relEntropy A B := by sorry

end MomentPolytopes.QuantumFunctionals
