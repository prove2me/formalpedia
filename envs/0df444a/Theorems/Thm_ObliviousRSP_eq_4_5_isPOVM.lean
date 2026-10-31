-- Prove2me | Theorems.Thm_ObliviousRSP_eq_4_5_isPOVM
-- name    : ObliviousRSP.eq_4_5_isPOVM
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:35.49986+00:00
-- url     : https://prove2.me/theorems/9dd01b7c-5004-4135-b6f6-a7fef20fbd60
-- title:
--   Eqs. (4)–(5) — $\{M_m\}$ is a POVM
-- statement:
--   Let $S$ be a generic ensemble and $(E,V,p,b)$ a faithful remote state preparation protocol oblivious to Bob for $S$. Then the operators
--   $$
--   M_m = d\,d'\,p_m\,\big(I\otimes V_m^{T}\big)\big(|\Phi_d\rangle\langle\Phi_d|\otimes b_m^{T}\big)\big(I\otimes \overline{V_m}\big)
--   $$
--   of (4) form a POVM on the specimen and Alice's half:
--
--   1. each $M_m$ is positive semidefinite, and
--   2. $\displaystyle\sum_m M_m = I\otimes I$, with unconditional convergence.
--
--   The measurement $\{M_m\}$ does not depend on the state to be prepared, which is what makes the modified protocol oblivious to Alice.
--
--   **Formalization Note** The page proves $\sum_m M_m^T = d d' (\mathcal F\otimes\mathcal I)(|\Phi_d\rangle\langle\Phi_d|) = I\otimes I$; its transpose is the POVM condition stated here. With (4) putting $U_m$ on registers 2, 3, $\mathcal F$ acts on the second factor of $|\Phi_d\rangle\langle\Phi_d|$; the value $I\otimes I$ is the same.
--
--   Differences from the source:
--   - encoding: ∑_m M_m^T = I ⊗ I → ∑_m M_m = 1 (HasSum); reason: the transpose is a continuous linear bijection fixing I ⊗ I; the two statements are equivalent
--   - encoding: M_m = d d′ p_m Tr_3 (I ⊗ U_m^T)(|Φ_d⟩⟨Φ_d| ⊗ b_m^T)(I ⊗ U_m^*) → povmElement V p b m, with V_m^T and the entrywise conjugate of V_m and no Tr_3; reason: for V_m = U_m(· ⊗ |0⟩) the Tr_3 over the one-dimensional ancilla leftover gives exactly this operator
--   - generalization: generic ensemble: the density matrices form a basis of the operators on the input space → IsGeneric S: unit vectors whose projectors span all ι × ι matrices; reason: every basis spans, so every generic ensemble of the paper satisfies IsGeneric
--   - generalization: Bob's recovery: unitary U_m on his half and a pure ancilla |0⟩ → any isometry V_m : ℂ^σ → ℂ^ι ⊗ ℂ^{K m}, with an output space K m per message, and no Tr_2; reason: U_m(· ⊗ |0⟩) is an isometry, so the paper's protocols are instances; for an isometry nothing is left over to trace
--   - reading: oblivious to Bob (p.2: Bob obtains no more information than the single specimen) → p_m and b_m^(out) do not depend on φ; reason: this is the consequence the paper draws from the oblivious condition on p.3 and the only form in which the proof uses it
--   - encoding: Alice's trace-preserving operation E_φ with classical output m → a POVM E ψ on her half with outcome type M; reason: the paper's own reduction on p.2: with only classical output, E_φ is a POVM
--   - generalization: sum over the messages m → HasSum over an arbitrary message type M; reason: covers finite and countably infinite message sets (p.5 allows messages of variable length); for a finite M it is the finite sum
--   - generalization: Alice's operation E_φ parameterized by the pure state φ → E ψ parameterized by a vector ψ with φ = |ψ⟩⟨ψ|; reason: every protocol of the paper is an instance (E ψ := E_φ for φ = |ψ⟩⟨ψ|); E may in addition depend on the global phase of ψ
-- source:
--   Leung–Shor, Oblivious remote state preparation, arXiv:quant-ph/0201008v1, eqs. (4)–(5), pp.3–4

import Mathlib
import Definitions.Def_WildeQIT_IsDensityOperator
import Definitions.Def_ObliviousRSP_pureState
import Definitions.Def_ObliviousRSP_IsPOVM
import Definitions.Def_ObliviousRSP_bobState
import Definitions.Def_ObliviousRSP_IsObliviousRSP
import Definitions.Def_ObliviousRSP_IsGeneric
import Definitions.Def_ObliviousRSP_povmElement

open scoped Kronecker Matrix

namespace ObliviousRSP

/-- Leung–Shor, *Oblivious remote state preparation*, arXiv:quant-ph/0201008v1, eqs. (4)–(5), pp.3–4: "Each Mm is manifestly positive. … Using Eq. (3),
∑m M^T_m = dd′(F ⊗ I)(|Φd⟩⟨Φd|) = I ⊗ I, so that {Mm} is indeed a POVM." For a faithful protocol
oblivious to Bob on a generic ensemble, the operators
`M_m = d d′ p_m (I ⊗ V_mᵀ)(|Φ_d⟩⟨Φ_d| ⊗ b_mᵀ)(I ⊗ V_m^*)` of (4) form a POVM on the specimen
and Alice's half: each is positive semidefinite and `∑_m M_m = I ⊗ I`.

**Formalization Note.** `M_m` is `povmElement V p b m` (no `Tr_3`, see its docstring). The page
sums the transposes `M_mᵀ`; the transpose of that identity is `∑_m M_m = I ⊗ I`, the POVM
condition stated here. The page writes `F ⊗ I` while (4) puts `U_m` on registers 2, 3, so `F` acts
on the second factor of `|Φ_d⟩⟨Φ_d|`; the value `I ⊗ I` is unaffected. -/
theorem eq_4_5_isPOVM {ι σ M : Type} [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {K : M → Type} [∀ m, Fintype (K m)] [∀ m, DecidableEq (K m)]
    {S : Set (ι → ℂ)} {E : (ι → ℂ) → M → Matrix σ σ ℂ} {V : (m : M) → Matrix (ι × K m) σ ℂ}
    {p : M → ℝ} {b : (m : M) → Matrix (K m) (K m) ℂ}
    (hS : IsGeneric S) (h : IsObliviousRSP S E V p b) :
    IsPOVM (povmElement V p b) := by sorry

end ObliviousRSP
