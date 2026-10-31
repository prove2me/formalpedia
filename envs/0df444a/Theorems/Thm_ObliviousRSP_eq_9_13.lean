-- Prove2me | Theorems.Thm_ObliviousRSP_eq_9_13
-- name    : ObliviousRSP.eq_9_13
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:36.663288+00:00
-- url     : https://prove2.me/theorems/3de00f6b-a233-4a2e-9b62-e9cad0d17256
-- title:
--   Eqs. (9)–(13) — the modified protocol gives Bob $\mathbf b = p_m\rho_{\varphi m}$
-- statement:
--   Let $(E,V,p,b)$ be a faithful remote state preparation protocol oblivious to Bob for an ensemble $S$, and let $M_m$ be the operators (4) built from $V$, $p$, $b$. Then for every $\psi\in S$, with $\varphi = |\psi\rangle\langle\psi|$, and every message $m$,
--   $$
--   \mathbf b = \operatorname{Tr}_{12}\big[(\varphi_1\otimes|\Phi_{d'}\rangle\langle\Phi_{d'}|_{23})(M_{m,12}\otimes I_3)\big] = p_m\,\rho_{\varphi m} .
--   $$
--
--   So when Alice applies the $\varphi$-independent measurement $\{M_m\}$ to a single specimen of $\varphi$ and her half of $|\Phi_{d'}\rangle$, each message occurs with the original probability $p_m$ and leaves Bob in the original state $\rho_{\varphi m}$.
--
--   **Formalization Note** Both sides are unnormalized (`modifiedBobState`, `bobState`). The chain (9)–(12) is proof; the final equality of (13) is stated.
--
--   Differences from the source:
--   - generalization: φ drawn from a generic ensemble (the standing assumption of the proof) → no genericity hypothesis on S; reason: (9)–(13) use only (1) and the form (4) of M_m, not genericity; the statement specializes to the paper's generic ensembles
--   - encoding: normalized conditional state ρ_φm → unnormalized p_m ρ_φm (bobState (E ψ m)); reason: ρ_φm is undefined when p_m = 0; for p_m > 0 dividing by p_m gives the page's identity, and the unnormalized state is the paper's own b of (6); same instances
--   - generalization: Bob's recovery: unitary U_m on his half and a pure ancilla |0⟩ → any isometry V_m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}, with an output space K m per message, and no Tr_2; reason: U_m(· ⊗ |0⟩) is an isometry, so the paper's protocols are instances; for an isometry nothing is left over to trace
--   - reading: oblivious to Bob (p.2: Bob obtains no more information than the single specimen) → p_m and b_m^(out) do not depend on φ; reason: this is the consequence the paper draws from the oblivious condition on p.3 and the only form in which the proof uses it
--   - encoding: Alice's trace-preserving operation E_φ with classical output m → a POVM E ψ on her half with outcome type M; reason: the paper's own reduction on p.2: with only classical output, E_φ is a POVM
--   - generalization: Alice's operation E_φ parameterized by the pure state φ → E ψ parameterized by a vector ψ with φ = |ψ⟩⟨ψ|; reason: every protocol of the paper is an instance (E ψ := E_φ for φ = |ψ⟩⟨ψ|); E may in addition depend on the global phase of ψ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eqs. (9)–(13), p.4

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP
import Definitions.Def_ObliviousRSP_povmElement
import Definitions.Def_ObliviousRSP_modifiedBobState

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eqs. (9)–(13), p.4: "So, the (j1, j2) entry of b is given by … = pm [ ρφm ]j1,j2 …
Thus b = pmρφm". For a faithful protocol oblivious to Bob, every `ψ ∈ S` and every message `m`,
Bob's unnormalized state when the modified measurement `{M_m}` of (4) is applied to the single
specimen `φ = |ψ⟩⟨ψ|` and Alice's half equals his unnormalized state `p_m ρ_φm` in the original
protocol.

**Formalization Note.** `M_m` is `povmElement V p b m`, **b** is `modifiedBobState`, and `p_m ρ_φm`
is `bobState (E ψ m)`. The chain (9)–(12) is proof; the final equality of (13) is stated. Genericity
of `S` is not assumed: (9)–(13) use only (1) and (4), so the identity holds for every ensemble on
which the protocol is faithful and oblivious to Bob. -/
theorem eq_9_13 {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (h : IsObliviousRSP S E V p b) {ψ : ι → ℂ} (hψ : ψ ∈ S) (m : M) :
    modifiedBobState (povmElement V p b m) (pureState ψ) = bobState (E ψ m) := by sorry

end ObliviousRSP
