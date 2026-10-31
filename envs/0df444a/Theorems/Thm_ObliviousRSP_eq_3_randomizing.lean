-- Prove2me | Theorems.Thm_ObliviousRSP_eq_3_randomizing
-- name    : ObliviousRSP.eq_3_randomizing
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:22.888468+00:00
-- url     : https://prove2.me/theorems/64a50670-5beb-44ca-a451-c6c0618e36db
-- title:
--   Eq. (3) — the operation $\mathcal F$ is the randomizing operation
-- statement:
--   Let $S$ be a generic ensemble and $(E,V,p,b)$ a faithful remote state preparation protocol oblivious to Bob for $S$. Define the operation
--   $$
--   \mathcal F(X) = \sum_m p_m\, V_m^\dagger\,(X\otimes b_m)\,V_m
--   $$
--   on operators $X$ on the input space. Then for **every** operator $X$,
--   $$
--   \mathcal F(X) = \operatorname{Tr}(X)\,\frac{I}{d'} ,
--   $$
--   with the series converging unconditionally. On the prepared states $\varphi$ (trace one) this is the paper's $\mathcal F(\varphi) = I/d'$ of (3), and genericity extends it to all operators: $\mathcal F$ is the randomizing operation.
--
--   This identity is what makes the modified measurement of (4) a POVM.
--
--   Differences from the source:
--   - reading: "F is defined for all operators … it is simply the randomizing operation, F(·) = I/d′" → F(X) = Tr(X) · I/d′ for every matrix X; reason: F is linear and equals I/d′ on the trace-one states, so its linear extension is X ↦ Tr(X) I/d′; the constant map I/d′ would not be linear
--   - generalization: generic ensemble: the density matrices form a basis of the operators on the input space → IsGeneric S: unit vectors whose projectors span all ι × ι matrices; reason: every basis spans, so every generic ensemble of the paper satisfies IsGeneric
--   - generalization: Bob's recovery: unitary U_m on his half and a pure ancilla |0⟩ → any isometry V_m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}, with an output space K m per message, and no Tr_2; reason: U_m(· ⊗ |0⟩) is an isometry, so the paper's protocols are instances; for an isometry nothing is left over to trace
--   - reading: oblivious to Bob (p.2: Bob obtains no more information than the single specimen) → p_m and b_m^(out) do not depend on φ; reason: this is the consequence the paper draws from the oblivious condition on p.3 and the only form in which the proof uses it
--   - encoding: Alice's trace-preserving operation E_φ with classical output m → a POVM E ψ on her half with outcome type M; reason: the paper's own reduction on p.2: with only classical output, E_φ is a POVM
--   - generalization: sum over the messages m → HasSum over an arbitrary message type M; reason: covers finite and countably infinite message sets (p.5 allows messages of variable length); for a finite M it is the finite sum
--   - generalization: Alice's operation E_φ parameterized by the pure state φ → E ψ parameterized by a vector ψ with φ = |ψ⟩⟨ψ|; reason: every protocol of the paper is an instance (E ψ := E_φ for φ = |ψ⟩⟨ψ|); E may in addition depend on the global phase of ψ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eq. (3) and the sentence after it, p.3

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP
import Definitions.Def_ObliviousRSP_IsGeneric

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eq. (3) and the sentence after it, p.3: "Equating the left side of Eq. (3) to F(φ)
defines an operation F acting on φ. Since the set of all possible φ forms a generic ensemble, F is
defined for all operators acting on the input Hilbert space, and it is simply the randomizing
operation, F(·) = I/d′." For a faithful protocol oblivious to Bob on a generic ensemble, the map
`F(X) = ∑_m p_m V_m† (X ⊗ b_m) V_m` sends **every** `X` on the input space to `Tr(X) · I/d′`.

**Formalization Note.** "F(·) = I/d′" is read as the linear extension `F(X) = Tr(X) I/d′` (on the
states φ, which have trace one, it is `I/d′`). The sum over messages is a `HasSum` over an
arbitrary type; `V m` is the paper's `U_m(· ⊗ |0⟩)`, so `Tr_2` is absent. -/
theorem eq_3_randomizing {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (hS : IsGeneric S) (h : IsObliviousRSP S E V p b) (X : Matrix ι ι ℂ) :
    HasSum (fun m => (p m : ℂ) • ((V m)ᴴ * (X ⊗ₖ b m) * V m))
      ((X.trace / (Fintype.card σ : ℂ)) • (1 : Matrix σ σ ℂ)) := by sorry

end ObliviousRSP
