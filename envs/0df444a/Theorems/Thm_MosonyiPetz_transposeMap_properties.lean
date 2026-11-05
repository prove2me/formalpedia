-- Prove2me | Theorems.Thm_MosonyiPetz_transposeMap_properties
-- name    : MosonyiPetz.transposeMap_properties
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:22.50476+00:00
-- url     : https://prove2.me/theorems/d30efa45-5ab7-4d21-96ad-efdcf3999b23
-- title:
--   Eq. (6): $T^\#$ is the trace-preserving standard dual of $\alpha$ and $T^\#(T(D_1))=D_1$
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   Let $T^\#(X)=D_1^{1/2}T^*\big(T(D_1)^{-1/2}XT(D_1)^{-1/2}\big)D_1^{1/2}$ (eq. (6)) and let $\alpha$ be the map (5). Then
--
--   1. $T^\#$ is the standard dual of $\alpha$: $\operatorname{Tr}T^\#(X)A=\operatorname{Tr}X\alpha(A)$ for all $X\in\mathcal B(\mathcal K)$, $A\in\mathcal B(\mathcal H)$;
--   2. $T^\#$ is trace preserving: $\operatorname{Tr}T^\#(X)=\operatorname{Tr}X$;
--   3. $T^\#(T(D_1))=D_1$.
--
--   So $T^\#$ always recovers $D_1$; Proposition 1 shows that under sufficiency it also recovers $D_2$.
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §2, p.4, eq. (6)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_MosonyiPetz_alpha
import Definitions.Def_MosonyiPetz_transposeMap

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace MosonyiPetz

/-- **T# of (6) is the trace-preserving standard dual of α, and T#(T(D₁)) = D₁.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §2, p.4, eq. (6): "The standard dual T# : B(K) → B(H) of α is trace preserving. ... Tr T#(X)A
= ⟨T#(X*), A⟩ = ⟨X*, α(A)⟩ = Tr Xα(A) = ... Hence T#(X) = D1^{1/2}T*(T(D1)^{−1/2}XT(D1)^{−1/2})D1^{1/2}.
(6) Observe that T#(T(D1)) = D1."

Under the standing assumption, the map `transposeMap T D₁` of (6) satisfies
1. `Tr (T#(X) A) = Tr (X α(A))` for all `X`, `A` (it is the standard dual of α);
2. `Tr T#(X) = Tr X` for all `X`;
3. `T#(T(D₁)) = D₁`.

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). -/
theorem transposeMap_properties
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef) :
    (∀ (X : Matrix K K ℂ) (A : Matrix H H ℂ),
      (transposeMap T (D 0) X * A).trace = (X * alpha T (D 0) A).trace) ∧
    (∀ X : Matrix K K ℂ, (transposeMap T (D 0) X).trace = X.trace) ∧
    transposeMap T (D 0) (T (D 0)) = D 0 := by sorry

end MosonyiPetz
