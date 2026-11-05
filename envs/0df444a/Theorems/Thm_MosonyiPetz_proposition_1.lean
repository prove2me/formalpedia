-- Prove2me | Theorems.Thm_MosonyiPetz_proposition_1
-- name    : MosonyiPetz.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:12.757666+00:00
-- url     : https://prove2.me/theorems/5a3e2737-0a6c-4f1d-95ca-83c10c91a634
-- title:
--   Proposition 1: under sufficiency $T^\#T(D_1)=D_1$ and $T^\#T(D_2)=D_2$
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   If there is a trace preserving 2-positive map $\beta:\mathcal B(\mathcal K)\to\mathcal B(\mathcal H)$ with $\beta T(D_1)=D_1$ and $\beta T(D_2)=D_2$ (that is, $T$ is sufficient for $D_1,D_2$), then the transpose map $T^\#$ of (6), built from $D_1$, recovers both densities:
--
--   $$T^\#T(D_1)=D_1\qquad\text{and}\qquad T^\#T(D_2)=D_2.$$
--
--   Among all recovery maps one can thus always choose the canonical $T^\#$. The paper deduces it from Petz's criterion (2) (Theorem 2 of its reference [14]) and the computation (7).
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §2, p.5, Proposition 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_transposeMap

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace MosonyiPetz

/-- **Proposition 1: sufficiency makes T# a recovery map for both densities.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §2, p.5, Proposition 1: "If there exists a trace preserving 2-positive mapping
β : B(K) → B(H) such that βT(D1) = D1 and βT(D2) = D2, then T#T(D1) = D1 and T#T(D2) = D2."

Under the standing assumption, if `T` is sufficient for `D₁`, `D₂` (eq. (1)), then
`T#(T(D₁)) = D₁` and `T#(T(D₂)) = D₂`, where `T#` is the map (6) built from `D₁`.

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

The paper proves it through Theorem 2 of its reference [14] (Petz), condition (2), and the
computation (7).

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). -/
theorem proposition_1
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    transposeMap T (D 0) (T (D 0)) = D 0 ∧ transposeMap T (D 0) (T (D 1)) = D 1 := by sorry

end MosonyiPetz
