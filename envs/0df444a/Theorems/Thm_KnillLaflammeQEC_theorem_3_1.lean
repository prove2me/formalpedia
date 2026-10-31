-- Prove2me | Theorems.Thm_KnillLaflammeQEC_theorem_3_1
-- name    : KnillLaflammeQEC.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:22:59.860975+00:00
-- url     : https://prove2.me/theorems/7ae7ecc3-06b2-4116-a030-41baa133dcbe
-- title:
--   Theorem 3.1 — $\mathcal A(\mathcal C,\mathcal R)$: $R_rA=\lambda_{r}I$ on $\mathcal C$, linearly closed, and corrected by $(\mathcal C,\mathcal R)$
-- statement:
--   Let $\mathcal C$ be a subspace of a finite-dimensional complex Hilbert space $\mathcal H$ and $\mathcal R=\{R_r\}$ a finite family of operators on $\mathcal H$. Let $\mathcal A(\mathcal C,\mathcal R)$ be the set of operators $A$ with $E(\mathcal C,\mathcal R\{A\})=0$. Then:
--
--   1. An operator $A$ belongs to $\mathcal A(\mathcal C,\mathcal R)$ if and only if, restricted to $\mathcal C$, each $R_rA$ is a multiple of the identity: for every $r$ there is $\lambda_r\in\mathbb C$ with
--   $$
--   R_rA|\Psi\rangle=\lambda_r|\Psi\rangle\qquad\text{for all }|\Psi\rangle\in\mathcal C.
--   $$
--   2. $\mathcal A(\mathcal C,\mathcal R)$ is linearly closed: it is a complex linear subspace of the operators on $\mathcal H$.
--   3. $(\mathcal C,\mathcal R)$ is $\mathcal A(\mathcal C,\mathcal R)$-correcting.
--
--   The first clause turns the error criterion into an algebraic one, which is the form used in the proof of the Knill–Laflamme conditions (Theorem 3.2); the second shows that a code correcting a set of interactions corrects their whole linear span.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - generalization: $\mathcal R$ a recovery superoperator ($\sum_r R_r^\dagger R_r=I$) → any finite family `R : K → Matrix ι ι ℂ`, no normalization; reason: the theorem holds without Eq.(5) (the proof never uses it); taking $\mathcal R$ a superoperator gives the paper's statement
--   - encoding: "when restricted to $\mathcal C$, $R_rA_a=\lambda_{ra}I$ for each $R_r\in\mathcal R$" → `∀ r, ∃ l : ℂ, ∀ ψ ∈ C, act (R r * A₀) ψ = l • ψ`; reason: literal meaning of the restriction to $\mathcal C$ being a multiple of the identity
--   - encoding: "$\mathcal A(\mathcal C,\mathcal R)$ is linearly closed" → there is a `Submodule ℂ (Matrix ι ι ℂ)` whose carrier is `correctableSet C R`; reason: a set of operators is linearly closed exactly when it is the carrier of a complex subspace
--   - encoding: "$(\mathcal C,\mathcal R)$ is $\mathcal A(\mathcal C,\mathcal R)$ correcting" → `IsCorrecting C R` of the family indexed by the elements of `correctableSet C R`; reason: the family $\mathcal A(\mathcal C,\mathcal R)$ indexed by its own members; `IsCorrecting` is the paper's per-operator form of $E=0$ (p.12)
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, Theorem 3.1, pp.12–13

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_KnillLaflammeQEC_codeError
import Definitions.Def_KnillLaflammeQEC_IsCorrecting
import Definitions.Def_KnillLaflammeQEC_correctableSet

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
Theorem 3.1, pp.12–13: "The operator `A_a` is in `A(C, R)` iff when restricted to `C`,
`R_r A_a = λ_ra I` for each `R_r ∈ R`. The family `A(C, R)` is linearly closed and `(C, R)` is
`A(C, R)` correcting."

The three clauses: (i) `A₀ ∈ A(C, R)` iff for every `r` there is a scalar `λ` with
`R_r A₀ ψ = λ ψ` for all `ψ ∈ C`; (ii) `A(C, R)` is a complex linear subspace of the operators;
(iii) `(C, R)` is `A(C, R)`-correcting, `A(C, R)` taken as a family indexed by its own elements.

**Formalization Note.** `H = EuclideanSpace ℂ ι`, operators `Matrix ι ι ℂ` acting by
`QAlgorithms.act`. The recovery is any finite family `R : K → Matrix ι ι ℂ`; the superoperator
constraint Eq.(5) on `R` is not assumed (the theorem holds without it, and the paper's recovery
superoperators are a special case). "Linearly closed" is stated as: `A(C, R)` is the carrier of a
`Submodule ℂ (Matrix ι ι ℂ)`. -/
theorem theorem_3_1 {ι K : Type*} [Fintype ι] [Fintype K]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (R : K → Matrix ι ι ℂ) :
    (∀ A₀ : Matrix ι ι ℂ, A₀ ∈ correctableSet C R ↔
        ∀ r, ∃ l : ℂ, ∀ ψ ∈ C, QAlgorithms.act (R r * A₀) ψ = l • ψ) ∧
      (∃ S : Submodule ℂ (Matrix ι ι ℂ), (S : Set (Matrix ι ι ℂ)) = correctableSet C R) ∧
      IsCorrecting C R (fun A₀ : correctableSet C R => (A₀ : Matrix ι ι ℂ)) := by sorry

end KnillLaflammeQEC
