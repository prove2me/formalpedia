-- Prove2me | Theorems.Thm_ObliviousRSP_eq_1
-- name    : ObliviousRSP.eq_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:32.718483+00:00
-- url     : https://prove2.me/theorems/ccdc028e-31df-4a1e-9974-f93dd4d04c0f
-- title:
--   Eq. (1) — Bob's conditional state through his recovery isometry
-- statement:
--   Let $(E,V,p,b)$ be a faithful remote state preparation protocol oblivious to Bob for an ensemble $S$. Then for every $\psi\in S$, with $\varphi = |\psi\rangle\langle\psi|$, and every message $m$, Bob's unnormalized conditional state satisfies
--   $$
--   p_m\,\rho_{\varphi m} = p_m\, V_m^\dagger\,(\varphi\otimes b_m)\,V_m .
--   $$
--
--   This expresses Bob's state before recovery in terms of the $\varphi$-independent data $V_m$, $p_m$, $b_m$; it is the input to (3) and (13).
--
--   **Formalization Note** The left side is `bobState (E ψ m)`. The paper's $\rho_{\varphi m} = \operatorname{Tr}_2[U_m^\dagger(\varphi\otimes b^{(out)}_m)U_m]$ appears without $\operatorname{Tr}_2$ because Bob's recovery is an isometry.
--
--   Differences from the source:
--   - encoding: normalized conditional state ρ_φm → unnormalized p_m ρ_φm (bobState (E ψ m)); reason: ρ_φm is undefined when p_m = 0; for p_m > 0 dividing by p_m gives the page's identity, and the unnormalized state is the paper's own b of (6); same instances
--   - generalization: Bob's recovery: unitary U_m on his half and a pure ancilla |0⟩ → any isometry V_m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}, with an output space K m per message, and no Tr_2; reason: U_m(· ⊗ |0⟩) is an isometry, so the paper's protocols are instances; for an isometry nothing is left over to trace
--   - reading: oblivious to Bob (p.2: Bob obtains no more information than the single specimen) → p_m and b_m^(out) do not depend on φ; reason: this is the consequence the paper draws from the oblivious condition on p.3 and the only form in which the proof uses it
--   - encoding: Alice's trace-preserving operation E_φ with classical output m → a POVM E ψ on her half with outcome type M; reason: the paper's own reduction on p.2: with only classical output, E_φ is a POVM
--   - generalization: φ drawn from a generic ensemble (the standing assumption on p.3) → any set S, with no genericity or unit-norm hypothesis; reason: (1) follows from the faithfulness identity and V_m† V_m = I alone; the statement specializes to the paper's generic ensembles
--   - generalization: Alice's operation E_φ parameterized by the pure state φ → E ψ parameterized by a vector ψ with φ = |ψ⟩⟨ψ|; reason: every protocol of the paper is an instance (E ψ := E_φ for φ = |ψ⟩⟨ψ|); E may in addition depend on the global phase of ψ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eq. (1), p.3

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eq. (1), p.3: "We obtain an expression for ρφm using the state change due to Um,
ρφm = Tr2 [ U†m ( φ ⊗ b(out)m ) Um ]". In unnormalized form: for a faithful protocol oblivious
to Bob, every `ψ ∈ S` and every message `m`, Bob's conditional state is
`bobState (E ψ m) = p_m · V_m† (φ ⊗ b_m) V_m` with `φ = |ψ⟩⟨ψ|`.

**Formalization Note.** Both sides are `p_m ρ_φm` (unnormalized). The paper's `U_m` with ancilla
`|0⟩` is the isometry `V m`; for an isometry nothing is left over, so `Tr_2` of (1) disappears. -/
theorem eq_1 {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (h : IsObliviousRSP S E V p b) {ψ : ι → ℂ} (hψ : ψ ∈ S) (m : M) :
    bobState (E ψ m) = (p m : ℂ) • ((V m)ᴴ * (pureState ψ ⊗ₖ b m) * V m) := by sorry

end ObliviousRSP
