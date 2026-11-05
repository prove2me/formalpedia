-- Prove2me | Theorems.Thm_MosonyiPetz_alpha_dual
-- name    : MosonyiPetz.alpha_dual
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:43:33.22781+00:00
-- url     : https://prove2.me/theorems/ff2b0d99-b682-4ae6-980d-faa89c66f684
-- title:
--   Eqs. (4)–(5): $\alpha$ is the unital 2-positive dual of $T^*$ for $\langle\cdot,\cdot\rangle_{D_1}$, $\langle\cdot,\cdot\rangle_{T(D_1)}$
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   Let $\alpha$ be the map (5), $\alpha(A)=T(D_1)^{-1/2}T(D_1^{1/2}AD_1^{1/2})T(D_1)^{-1/2}$, and $\langle A,B\rangle_D=\operatorname{Tr}A^*D^{1/2}BD^{1/2}$. Then
--
--   1. $\alpha$ is the dual of $T^*$ for these inner products:
--   $$\langle X,\alpha(A)\rangle_{T(D_1)}=\langle T^*(X),A\rangle_{D_1}\qquad(A\in\mathcal B(\mathcal H),\ X\in\mathcal B(\mathcal K));\tag{4}$$
--   2. $\alpha$ is the only map with property (4);
--   3. $\alpha$ is unital, $\alpha(I)=I$;
--   4. $\alpha$ is 2-positive.
--
--   The map $\alpha$ is the paper's main tool: its fixed-point structure with $T^*$ yields the algebras $\mathcal D_{\mathcal H}$, $\mathcal D_{\mathcal K}$.
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
--   - reading: α is characterized by the properties (4) → clause 2: every map φ with (4) equals alpha T D₁; reason: 'characterized' asserts uniqueness; stating it is the stronger reading
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §2, pp.3–4, eqs. (4)–(5)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_alpha
import Definitions.Def_MosonyiPetz_weightedInner

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **The map α of (5) is the 2-positive unital dual of T* characterized by (4).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §2, pp.3–4, eqs. (4)–(5): "The dual α of T* with respect to these inner products is 2-positive
and unital, and it is characterized by the properties α : B(H) → B(K),
⟨X, α(A)⟩_{T(D1)} = ⟨T*(X), A⟩_{D1} (A ∈ B(H), X ∈ B(K)). (4) It is easy to give α concretely:
α(A) = T(D1)^{−1/2}T(D1^{1/2}AD1^{1/2})T(D1)^{−1/2} (5)".

Under the standing assumption, the map `alpha T D₁` of (5) satisfies
1. the duality (4): `⟨X, α A⟩_{T(D₁)} = ⟨T* X, A⟩_{D₁}` for all `A`, `X`;
2. it is the only map with (4);
3. `α 1 = 1`;
4. `α` is 2-positive.

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). -/
theorem alpha_dual
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef) :
    (∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
      weightedInner (T (D 0)) X (alpha T (D 0) A) =
        weightedInner (D 0) (channelAdjoint T X) A) ∧
    (∀ φ : Matrix H H ℂ → Matrix K K ℂ,
      (∀ (A : Matrix H H ℂ) (X : Matrix K K ℂ),
        weightedInner (T (D 0)) X (φ A) = weightedInner (D 0) (channelAdjoint T X) A) →
      φ = alpha T (D 0)) ∧
    alpha T (D 0) 1 = 1 ∧ IsTwoPositive (alpha T (D 0)) := by sorry

end MosonyiPetz
