-- Prove2me | Theorems.Thm_KnillLaflammeQEC_forward_computation
-- name    : KnillLaflammeQEC.forward_computation
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:50.189357+00:00
-- url     : https://prove2.me/theorems/37404a7f-e7fd-4170-934d-7a7c38b7521f
-- title:
--   Proof of Theorem 3.2, p.14 — an $\mathcal A$-correcting code has $\langle i_L|A_a^\dagger A_b|j_L\rangle=\alpha_{ab}\delta_{ij}$
-- statement:
--   Let $\mathcal C$ be a subspace of a finite-dimensional complex Hilbert space $\mathcal H$, $\mathcal A=\{A_a\}_{a\in\alpha}$ an arbitrary family of operators on $\mathcal H$, and $\mathcal R=\{R_r\}$ a recovery superoperator, i.e. a finite family with $\sum_r R_r^\dagger R_r=I$, such that $(\mathcal C,\mathcal R)$ is $\mathcal A$-correcting. Let $\{|i_L\rangle\}$ be an orthonormal basis of $\mathcal C$. Then there are numbers $\alpha_{ab}\in\mathbb C$, not depending on $i,j$, with
--
--   $$
--   \langle i_L|A_a^\dagger A_b|j_L\rangle=\alpha_{ab}\,\delta_{ij}\qquad\text{for all }a,b\text{ and all }i,j.
--   $$
--
--   This is the forward ("only if") direction of the Knill–Laflamme conditions with the common diagonal value made explicit: it gives (19) and (20) at once.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - encoding: an orthonormal basis $|i_L\rangle$ of $\mathcal C$ → an orthonormal family `e : κ → H` with `Submodule.span ℂ (Set.range e) = C`; reason: an orthonormal family spanning $\mathcal C$ is exactly an orthonormal basis of $\mathcal C$; `κ` is then automatically finite
--   - reading: a recovery superoperator $\mathcal R=\{R_r\}$ with $\sum_r R_r^\dagger R_r=I$ (Eq.(5)), index set unspecified → a finite family `R : K → Matrix ι ι ℂ` indexed by a finite type `K` with `QAlgorithms.IsKrausFamily R` ($\sum_r R_r^\dagger R_r=I$); reason: every superoperator on a finite-dimensional space has a finite set of interaction operators, and the paper's own recovery (22) is finite
--   - encoding: $(\mathcal C,\mathcal R)$ is $\mathcal A$-correcting: $E(\mathcal C,\mathcal R\mathcal A)=\max_{|\Psi\rangle\in\mathcal C}\sum_{r,a}|(R_rA_a-\langle\Psi|R_rA_a|\Psi\rangle)|\Psi\rangle|^2=0$ → `IsCorrecting C R A`: for every `a`, the real `sSup` over unit vectors `ψ ∈ C` of $\sum_r\|R_rA_a\psi-\langle\psi|R_rA_a|\psi\rangle\psi\|^2$ is `0`; reason: this is the paper's own equivalent per-operator form (p.12), the one it uses for infinite $\mathcal A$; the set is bounded (continuous function on a compact sphere), so `sSup` is the max, and for $\mathcal C=0$ the empty set gives `0`, where every recovery corrects
--   - encoding: $\langle i_L|A_a^\dagger A_b|j_L\rangle=\alpha_{ab}\delta_{ij}$ with $\alpha_{ab}$ independent of $i,j$ → `∃ c : α → α → ℂ, ∀ a b i j, inner ℂ (e i) (act ((A a)ᴴ * A b) (e j)) = if i = j then c a b else 0`; reason: $\delta_{ij}$ written as `if i = j`; `c` is $\alpha_{ab}$
--   - encoding: basis index set with no further structure → `[DecidableEq κ]`; reason: needed only to write `if i = j`; every type has decidable equality classically, so no instance is excluded
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, proof of Theorem 3.2, p.14

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_KnillLaflammeQEC_IsCorrecting
open scoped Matrix

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
proof of Theorem 3.2 (forward direction), p.14: if `(C, R)` is an `A`-correcting code with `R`
a superoperator, then for an orthonormal basis `|i_L⟩` of `C`,
`⟨i_L|A_a† A_b|j_L⟩ = Σ_r ⟨i_L|λ̄_ra λ_rb|j_L⟩ = α_ab δ_ij`, with `α_ab` independent of `i, j`.

**Formalization Note.** `H = EuclideanSpace ℂ ι`, operators `Matrix ι ι ℂ` acting by
`QAlgorithms.act`, `⟨x|X|y⟩ = inner ℂ x (act X y)` (conjugate-linear in the first slot). The
recovery superoperator is a finite Kraus family (`QAlgorithms.IsKrausFamily R`,
`Σ_r R_r† R_r = I`, Eq.(5)). The family `A` is arbitrary (any index type, no normalization).
The orthonormal basis of `C` is an orthonormal family `e : κ → H` whose span is `C`. The
existential `c` is the paper's `α_ab`. -/
theorem forward_computation {ι K α κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype K]
    [DecidableEq κ]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (R : K → Matrix ι ι ℂ) (A : α → Matrix ι ι ℂ)
    (hR : QAlgorithms.IsKrausFamily R) (hA : IsCorrecting C R A)
    (e : κ → EuclideanSpace ℂ ι) (he : Orthonormal ℂ e)
    (hspan : Submodule.span ℂ (Set.range e) = C) :
    ∃ c : α → α → ℂ, ∀ (a b : α) (i j : κ),
      inner ℂ (e i) (QAlgorithms.act ((A a)ᴴ * A b) (e j)) = if i = j then c a b else 0 := by sorry

end KnillLaflammeQEC
