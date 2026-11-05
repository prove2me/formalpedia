-- Prove2me | Theorems.Thm_MosonyiPetz_lemma_1
-- name    : MosonyiPetz.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:50.107947+00:00
-- url     : https://prove2.me/theorems/2e727558-e56e-41f4-a404-42634a599a5f
-- title:
--   Lemma 1: $\mathcal D_K\subset\mathcal A_{T^*}$, $\mathcal D_H\subset\mathcal A_\alpha$, $T^*:\mathcal D_K\to\mathcal D_H$ is an isomorphism with inverse $\alpha$, and (10)
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   Assume that $T$ is sufficient for $D_1,D_2$. Let $\mathcal D_{\mathcal K}$, $\mathcal D_{\mathcal H}$ be the fixed-point sets of $\gamma_{\mathcal K}=\alpha\circ T^*$ and $\gamma_{\mathcal H}=T^*\circ\alpha$, and
--
--   $$\mathcal A_{T^*}=\{X:\ T^*(XX^*)=T^*(X)T^*(X^*),\ T^*(X^*X)=T^*(X^*)T^*(X)\},$$
--   $$\mathcal A_\alpha=\{A:\ \alpha(AA^*)=\alpha(A)\alpha(A^*),\ \alpha(A^*A)=\alpha(A^*)\alpha(A)\}.$$
--
--   Then
--
--   1. $\mathcal D_{\mathcal K}\subset\mathcal A_{T^*}$;
--   2. $\mathcal D_{\mathcal H}\subset\mathcal A_\alpha$;
--   3. $T^*$ restricted to $\mathcal D_{\mathcal K}$ is an algebra isomorphism onto $\mathcal D_{\mathcal H}$ with inverse $\alpha$: both sets are closed under multiplication, $T^*$ maps $\mathcal D_{\mathcal K}$ onto $\mathcal D_{\mathcal H}$, $T^*(XY)=T^*(X)T^*(Y)$ for $X,Y\in\mathcal D_{\mathcal K}$, $\alpha(T^*(X))=X$ on $\mathcal D_{\mathcal K}$ and $T^*(\alpha(A))=A$ on $\mathcal D_{\mathcal H}$;
--   4. for all $A\in\mathcal A_\alpha$ and $B\in\mathcal B(\mathcal H)$,
--   $$\alpha(AB)=\alpha(A)\alpha(B).\tag{10}$$
--
--   The paper does not prove the lemma; it refers to 9.1 of Strătilă, *Modular theory in operator algebras* (its reference [17]); (10) is Choi's multiplicative-domain theorem for the unital 2-positive map $\alpha$.
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
--   - reading: T* restricted to D_K is an algebraic isomorphism onto D_H with inverse α → D_K, D_H closed under products; T* maps D_K onto D_H, is multiplicative on D_K; α ∘ T* = id on D_K and T* ∘ α = id on D_H; reason: spells out 'algebraic isomorphism' between the fixed point algebras (p.8); T* is linear by construction
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.8, Lemma 1

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_alpha
import Definitions.Def_MosonyiPetz_fixedPointsH
import Definitions.Def_MosonyiPetz_fixedPointsK
import Definitions.Def_MosonyiPetz_schwarzDomain

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)
open QAlgorithms.Papers.Independent.Dependency50.P21 (channelAdjoint)

namespace MosonyiPetz

/-- **Lemma 1: the fixed-point algebras lie in the multiplicative domains, and T* : D_K → D_H is
an algebra isomorphism with inverse α.**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.8, Lemma 1: "Let A_{T*} := {X ∈ B(K) : T*(XX*) = T*(X)T*(X*) and T*(X*X) = T*(X*)T*(X)}
and A_α := {A ∈ B(H) : α(AA*) = α(A)α(A*) and α(A*A) = α(A*)α(A)}. Then DK ⊂ A_{T*} and
DH ⊂ A_α. Moreover, T* restricted to DK is an algebraic isomorphism onto DH with inverse α and
α(AB) = α(A)α(B) (10) for all A ∈ A_α and B ∈ B(H)."

Under the standing assumption and sufficiency (§4), with `D_K`, `D_H` the fixed-point sets of
`γ_K = α ∘ T*` and `γ_H = T* ∘ α`:
1. `D_K ⊆ A_{T*}`;
2. `D_H ⊆ A_α`;
3. `D_K` and `D_H` are closed under multiplication, `T*` maps `D_K` onto `D_H`, `T*` is
   multiplicative on `D_K`, `α (T* X) = X` for `X ∈ D_K` and `T* (α A) = A` for `A ∈ D_H`;
4. (10): `α (A B) = α A * α B` for every `A ∈ A_α` and every `B`.

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

The paper does not prove the lemma ("concerning the proof see 9.1 in [17]", Strătilă, *Modular theory in operator algebras*). (10) is Choi's
multiplicative-domain theorem for the unital 2-positive map α.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). "Algebraic isomorphism onto D_H" is read as: `D_K`, `D_H` closed under products (they are
the "fixed point algebras" of p.8), `T*` (linear by construction) multiplicative on `D_K`,
mapping `D_K` onto `D_H`, with two-sided inverse α. -/
theorem lemma_1
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    fixedPointsK T (D 0) ⊆ schwarzDomain (channelAdjoint T) ∧
    fixedPointsH T (D 0) ⊆ schwarzDomain (alpha T (D 0)) ∧
    ((∀ X ∈ fixedPointsK T (D 0), ∀ Y ∈ fixedPointsK T (D 0), X * Y ∈ fixedPointsK T (D 0)) ∧
      (∀ A ∈ fixedPointsH T (D 0), ∀ B ∈ fixedPointsH T (D 0), A * B ∈ fixedPointsH T (D 0)) ∧
      (∀ X ∈ fixedPointsK T (D 0), channelAdjoint T X ∈ fixedPointsH T (D 0)) ∧
      (∀ A ∈ fixedPointsH T (D 0), ∃ X ∈ fixedPointsK T (D 0), channelAdjoint T X = A) ∧
      (∀ X ∈ fixedPointsK T (D 0), ∀ Y ∈ fixedPointsK T (D 0),
        channelAdjoint T (X * Y) = channelAdjoint T X * channelAdjoint T Y) ∧
      (∀ X ∈ fixedPointsK T (D 0), alpha T (D 0) (channelAdjoint T X) = X) ∧
      (∀ A ∈ fixedPointsH T (D 0), channelAdjoint T (alpha T (D 0) A) = A)) ∧
    ∀ A ∈ schwarzDomain (alpha T (D 0)), ∀ B : Matrix H H ℂ,
      alpha T (D 0) (A * B) = alpha T (D 0) A * alpha T (D 0) B := by sorry

end MosonyiPetz
