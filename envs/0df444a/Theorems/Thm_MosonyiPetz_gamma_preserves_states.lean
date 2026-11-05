-- Prove2me | Theorems.Thm_MosonyiPetz_gamma_preserves_states
-- name    : MosonyiPetz.gamma_preserves_states
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:44:59.557391+00:00
-- url     : https://prove2.me/theorems/d9b3dd2f-5445-4945-add7-84e65fd9a414
-- title:
--   $\gamma_{\mathcal H}$, $\gamma_{\mathcal K}$ preserve the states of $D_s$ and $T(D_s)$
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   Assume that $T$ is sufficient for $D_1,D_2$, and let $\gamma_{\mathcal H}=T^*\circ\alpha$ and $\gamma_{\mathcal K}=\alpha\circ T^*$. Then for $s=1,2$, every $A\in\mathcal B(\mathcal H)$ and every $X\in\mathcal B(\mathcal K)$,
--
--   $$\operatorname{Tr}D_s\gamma_{\mathcal H}(A)=\operatorname{Tr}D_sA,\qquad \operatorname{Tr}T(D_s)\gamma_{\mathcal K}(X)=\operatorname{Tr}T(D_s)X.$$
--
--   These four invariances are what makes the fixed-point sets $\mathcal D_{\mathcal H}$, $\mathcal D_{\mathcal K}$ algebras with faithful invariant states.
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.8, display before Lemma 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_gammaH
import Definitions.Def_MosonyiPetz_gammaK

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)

namespace MosonyiPetz

/-- **γ_H and γ_K leave the states of D₁, D₂ and of T(D₁), T(D₂) invariant.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8, display before Lemma 1: "The mapping γH leaves the state corresponding to D1
invariant: Tr D1γH(A) = Tr D1A follows by easy computation. Tr D2γH(A) = Tr D2A was shown in the
equivalent form T#(T(D2)) = D2 in (7). Similarly, Tr T(D1)γK(X) = Tr T(D1)X and
Tr T(D2)γK(X) = Tr T(D2)X."

Under the standing assumption and sufficiency (§4: "we suppose that T is sufficient for D1 and
D2"), for `s = 1, 2`, every `A ∈ B(H)` and every `X ∈ B(K)`:
`Tr (D_s γ_H(A)) = Tr (D_s A)` and `Tr (T(D_s) γ_K(X)) = Tr (T(D_s) X)` (four identities).

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). -/
theorem gamma_preserves_states
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    (∀ (s : Fin 2) (A : Matrix H H ℂ),
      (D s * gammaH T (D 0) A).trace = (D s * A).trace) ∧
    (∀ (s : Fin 2) (X : Matrix K K ℂ),
      (T (D s) * gammaK T (D 0) X).trace = (T (D s) * X).trace) := by sorry

end MosonyiPetz
