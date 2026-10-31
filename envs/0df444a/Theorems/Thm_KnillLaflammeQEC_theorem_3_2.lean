-- Prove2me | Theorems.Thm_KnillLaflammeQEC_theorem_3_2
-- name    : KnillLaflammeQEC.theorem_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:12.955185+00:00
-- url     : https://prove2.me/theorems/6db9f6cc-250d-4cdd-b46d-e57d34dbf04e
-- title:
--   Theorem 3.2 — Knill–Laflamme conditions: $\mathcal C$ extends to an $\mathcal A$-correcting code iff (19) and (20)
-- statement:
--   Let $\mathcal H$ be a finite-dimensional complex Hilbert space, $\mathcal C\subseteq\mathcal H$ a subspace (a quantum code of any dimension), $\mathcal A=\{A_a\}_{a\in\alpha}$ an arbitrary family of operators on $\mathcal H$ (possibly infinite, not required to satisfy $\sum_aA_a^\dagger A_a=I$), and $\{|i_L\rangle\}$ an orthonormal basis of $\mathcal C$. Then $\mathcal C$ can be extended to an $\mathcal A$-correcting code, i.e. there is a recovery superoperator $\mathcal R=\{R_r\}$ ($\sum_rR_r^\dagger R_r=I$) such that $(\mathcal C,\mathcal R)$ is $\mathcal A$-correcting, if and only if for all basis elements $|i_L\rangle,|j_L\rangle$ with $i\ne j$ and all operators $A_a,A_b\in\mathcal A$
--
--   $$
--   \langle i_L|A_a^\dagger A_b|i_L\rangle=\langle j_L|A_a^\dagger A_b|j_L\rangle \qquad (19)
--   $$
--
--   and
--
--   $$
--   \langle i_L|A_a^\dagger A_b|j_L\rangle=0. \qquad (20)
--   $$
--
--   The conditions do not mention the recovery operator, so they allow $\mathcal A$-correcting codes to be defined, and searched for, from the code alone; they hold for one orthonormal basis of $\mathcal C$ exactly when they hold for every one.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - encoding: an orthonormal basis $|i_L\rangle$ of $\mathcal C$ → an orthonormal family `e : κ → H` with `Submodule.span ℂ (Set.range e) = C`; reason: an orthonormal family spanning $\mathcal C$ is exactly an orthonormal basis of $\mathcal C$; `κ` is then automatically finite
--   - reading: a recovery superoperator $\mathcal R=\{R_r\}$ with $\sum_r R_r^\dagger R_r=I$ (Eq.(5)), index set unspecified → a finite family `R : Fin m → Matrix ι ι ℂ` for some `m : ℕ` with `QAlgorithms.IsKrausFamily R` ($\sum_r R_r^\dagger R_r=I$); reason: every superoperator on a finite-dimensional space has a finite set of interaction operators, and the paper's own recovery (22) is finite
--   - encoding: $(\mathcal C,\mathcal R)$ is $\mathcal A$-correcting: $E(\mathcal C,\mathcal R\mathcal A)=\max_{|\Psi\rangle\in\mathcal C}\sum_{r,a}|(R_rA_a-\langle\Psi|R_rA_a|\Psi\rangle)|\Psi\rangle|^2=0$ → `IsCorrecting C R A`: for every `a`, the real `sSup` over unit vectors `ψ ∈ C` of $\sum_r\|R_rA_a\psi-\langle\psi|R_rA_a|\psi\rangle\psi\|^2$ is `0`; reason: this is the paper's own equivalent per-operator form (p.12), the one it uses for infinite $\mathcal A$; the set is bounded (continuous function on a compact sphere), so `sSup` is the max, and for $\mathcal C=0$ the empty set gives `0`, where every recovery corrects
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, Theorem 3.2, p.13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Channel
import Definitions.Def_KnillLaflammeQEC_IsCorrecting
open scoped Matrix

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
Theorem 3.2, p.13: "The code `C` can be extended to an `A`-correcting code iff for all basis
elements `|i_L⟩, |j_L⟩` (`i ≠ j`) and operators `A_a, A_b` in `A`
`⟨i_L|A_a† A_b|i_L⟩ = ⟨j_L|A_a† A_b|j_L⟩` (19) and `⟨i_L|A_a† A_b|j_L⟩ = 0` (20)", where `|i_L⟩`
are the elements of an orthonormal basis of `C` (p.13).

**Formalization Note.** The coding space is `H = EuclideanSpace ℂ ι` for a finite type `ι`
(any dimension `n`); `C` is any subspace (any dimension `k`, including `0` and `1`). Operators
are matrices `Matrix ι ι ℂ` acting by `QAlgorithms.act`; `⟨x|X|y⟩` is `inner ℂ x (act X y)`
(conjugate-linear in the first slot). "Extended to an `A`-correcting code" means: there is a
recovery superoperator `R` such that `(C, R)` is `A`-correcting; `R` is a finite Kraus family
`Fin m → Matrix ι ι ℂ` with `Σ_r R_r† R_r = I` (Eq.(5)), which covers every superoperator on a
finite-dimensional space. `A : α → Matrix ι ι ℂ` is an arbitrary family (any index type,
possibly infinite, no normalization), and `A`-correcting is `KnillLaflammeQEC.IsCorrecting`
(the paper's per-operator form, p.12). The orthonormal basis is any orthonormal family
`e : κ → H` whose span is `C`; the statement holds for every such basis. -/
theorem theorem_3_2 {ι α κ : Type*} [Fintype ι] [DecidableEq ι]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (A : α → Matrix ι ι ℂ)
    (e : κ → EuclideanSpace ℂ ι) (he : Orthonormal ℂ e)
    (hspan : Submodule.span ℂ (Set.range e) = C) :
    (∃ (m : ℕ) (R : Fin m → Matrix ι ι ℂ), QAlgorithms.IsKrausFamily R ∧ IsCorrecting C R A) ↔
      ∀ i j : κ, i ≠ j → ∀ a b : α,
        inner ℂ (e i) (QAlgorithms.act ((A a)ᴴ * A b) (e i)) =
            inner ℂ (e j) (QAlgorithms.act ((A a)ᴴ * A b) (e j)) ∧
          inner ℂ (e i) (QAlgorithms.act ((A a)ᴴ * A b) (e j)) = 0 := by sorry

end KnillLaflammeQEC
