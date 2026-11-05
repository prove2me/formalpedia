-- Prove2me | Theorems.Thm_MosonyiPetz_modular_invariance
-- name    : MosonyiPetz.modular_invariance
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:46:41.394539+00:00
-- url     : https://prove2.me/theorems/95cdc2c7-9a26-49ec-bbb5-d02365e59f5b
-- title:
--   $T(D_s)^{it}\mathcal D_{\mathcal K}T(D_s)^{-it}\subset\mathcal D_{\mathcal K}$ for $s=1,2$
-- statement:
--   Throughout, $T:\mathcal B(\mathcal H)\to\mathcal B(\mathcal K)$ is a linear, trace-preserving, 2-positive map between the matrix algebras of finite-dimensional Hilbert spaces, and $D_1,D_2$ are invertible density matrices on $\mathcal H$ with $T(D_1)$, $T(D_2)$ invertible (the standing assumption of the paper, p.3). $T^*$ is the adjoint of $T$ for the Hilbert–Schmidt inner product $\langle A,B\rangle=\operatorname{Tr}A^*B$.
--
--   Assume that $T$ is sufficient for $D_1,D_2$ and let $\mathcal D_{\mathcal K}$ be the fixed-point set of $\gamma_{\mathcal K}=\alpha\circ T^*$. Then $\mathcal D_{\mathcal K}$ is invariant under the modular groups of both output densities: for $s=1,2$ and every real $t$,
--
--   $$T(D_s)^{it}\,\mathcal D_{\mathcal K}\,T(D_s)^{-it}\subset\mathcal D_{\mathcal K}.$$
--
--   With Propositions 2–4 this forces each unitary $T(D_s)^{it}$, hence $T(D_s)$, to be block diagonal along the central blocks of $\mathcal D_{\mathcal K}$ (p.9).
--
--   **Formalization Note** $\mathcal B(\mathcal H)$ is `Matrix H H ℂ` for a finite index type `H`; the densities are `D 0` $=D_1$ and `D 1` $=D_2$; an invertible density is a positive definite matrix of trace one; $T^*$ is the published Hilbert–Schmidt adjoint `channelAdjoint`. Square roots are the continuous functional calculus of $\sqrt{x}$ and $(\sqrt x)^{-1}$. $T(D_s)^{it}$ is the published `imaginaryPower`, $e^{it\log T(D_s)}$ on the positive definite $T(D_s)$.
--
--   Differences from the source:
--   - encoding: the two densities D_1, D_2 (s = 1, 2) → D : Fin 2 → Matrix H H ℂ with D 0 = D₁, D 1 = D₂; reason: indexing convention; same instances
--   - encoding: invertible density matrices D_s and invertible T(D_s) → (D s).PosDef ∧ (D s).trace = 1 and (T (D s)).PosDef; reason: an invertible positive semidefinite matrix is positive definite; same instances
--   - encoding: T*, the adjoint of T for ⟨A, B⟩ = Tr A*B → channelAdjoint T (published Hilbert–Schmidt adjoint); reason: the same map
--   - encoding: T(D_s)^{it} → imaginaryPower (T (D s)) t; reason: spectral calculus of x ↦ x^{it} on the support; equals exp(it log T(D_s)) on the positive definite T(D_s)
--   - generalization: T(D1)^{it} D_K T(D1)^{−it} ⊂ D_K → the same for T(D_1) and T(D_2) (all s : Fin 2); reason: 'Similar argument applies to T(D2)' (p.9); γ_K preserves the faithful state T(D_2) as well (p.8); at s = 0 it is the printed statement
-- source:
--   Mosonyi–Petz, Structure of sufficient quantum coarse-grainings, arXiv:quant-ph/0312221v1, §4, p.9, first paragraph

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P84
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P21
import Definitions.Def_MosonyiPetz_IsSufficient
import Definitions.Def_MosonyiPetz_fixedPointsK

open scoped Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Intakethird100.P84 (IsTwoPositive)
open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

namespace MosonyiPetz

/-- **D_K is invariant under the modular groups of T(D₁) and T(D₂).**
Mosonyi–Petz, *Structure of sufficient quantum coarse-grainings*, arXiv:quant-ph/0312221v1, §4, p.9, first paragraph: "We have T(D1)^{it}D_K T(D1)^{−it} ⊂ D_K and to the unitaries
T(D1)^{it} we can apply the arguments in the previous section." and, for the second density,
"Similar argument applies to T(D2)".

Under the standing assumption and sufficiency (§4), for `s = 1, 2`, every real `t` and every
`X ∈ D_K`: `T(D_s)^{it} X T(D_s)^{−it} ∈ D_K`.

The standing assumption of the paper (p.3: "T always denotes a trace-preserving 2-positive
mapping T : B(H) → B(K) and we assume that the density matrices D1, D2, T(D1) and T(D2) are all
invertible") is in the binders: `T` is `ℂ`-linear, 2-positive (`IsTwoPositive`) and trace
preserving, and `D 0 = D₁`, `D 1 = D₂` are positive definite of trace one with `T (D s)` positive
definite.

The paper's justification is Takesaki's theorem (p.5, around (8)), applied on the K side.

**Formalization Note.** `B(H)` is `Matrix H H ℂ` for a finite index type `H`. The two densities
are indexed by `Fin 2` (`D 0 = D₁`, `D 1 = D₂`); an invertible density is a positive definite matrix
of trace one. `T*` is the Hilbert–Schmidt adjoint `channelAdjoint T`. The maps α, T#, γ_H, γ_K and the
sets D_H, D_K are built from `D₁ = D 0`, as in the paper (p.4). `T(D_s)^{it}` is `imaginaryPower (T (D s)) t` (published bundle
`QAlgorithms.Papers.Independent.Dependency50.P21`), i.e. `exp(i t log T(D_s))` on the positive
definite `T(D_s)`. -/
theorem modular_invariance
    {H K : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
    (T : Matrix H H ℂ →ₗ[ℂ] Matrix K K ℂ) (hT : IsTwoPositive T)
    (htr : ∀ A, (T A).trace = A.trace)
    (D : Fin 2 → Matrix H H ℂ) (hD : ∀ s, (D s).PosDef ∧ (D s).trace = 1)
    (hTD : ∀ s, (T (D s)).PosDef)
    (hsuff : IsSufficient T (D 0) (D 1)) :
    ∀ (s : Fin 2) (t : ℝ), ∀ X ∈ fixedPointsK T (D 0),
      imaginaryPower (T (D s)) t * X * imaginaryPower (T (D s)) (-t) ∈ fixedPointsK T (D 0) := by sorry

end MosonyiPetz
