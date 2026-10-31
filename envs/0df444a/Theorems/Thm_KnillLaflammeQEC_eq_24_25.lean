-- Prove2me | Theorems.Thm_KnillLaflammeQEC_eq_24_25
-- name    : KnillLaflammeQEC.eq_24_25
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:21:19.543976+00:00
-- url     : https://prove2.me/theorems/8d2e9415-7e5e-4413-bad0-0cc8ee9bad90
-- title:
--   Eqs. (24)–(25), p.15 — the constructed recovery gives $R_rA_a|\Psi\rangle=\beta^0_{ar}|\Psi\rangle$ and $\mathcal O A_a|\Psi\rangle=0$
-- statement:
--   Let $\mathcal C$ be a subspace of a finite-dimensional complex Hilbert space $\mathcal H$ with orthonormal basis $\{|i_L\rangle\}_{i\in\kappa}$ and a distinguished element $|0_L\rangle$, and let $\{A_a\}_{a\in\alpha}$ be a family of operators satisfying condition (20), $\langle i_L|A_a^\dagger A_b|j_L\rangle=0$ for $i\ne j$. Assume the data of the construction in the proof of Theorem 3.2:
--
--   1. unitaries $U_i$ with $U_iA_a|0_L\rangle=A_a|i_L\rangle$ for all $a$ and $i$;
--   2. an orthonormal basis $\{|\nu^0_r\rangle\}$ of $\mathcal V^0=\operatorname{span}\{A_a|0_L\rangle\}$, and $|\nu^i_r\rangle:=U_i|\nu^0_r\rangle$;
--   3. unitaries $V_r$ with $V_r|\nu^i_r\rangle=|i_L\rangle$ for all $i$ (Eq.(21));
--   4. $R_r=V_r\sum_i|\nu^i_r\rangle\langle\nu^i_r|$ (Eq.(23)) and $\mathcal O=I-\sum_{i,r}|\nu^i_r\rangle\langle\nu^i_r|$.
--
--   Then for every $|\Psi\rangle\in\mathcal C$, every $a$ and every $r$,
--
--   $$
--   R_rA_a|\Psi\rangle=\beta^0_{ar}|\Psi\rangle\quad\text{with }\beta^0_{ar}=\langle\nu^0_r|A_a|0_L\rangle,\qquad\text{and}\qquad \mathcal O A_a|\Psi\rangle=0 .
--   $$
--
--   These are Eqs.(24)–(25) and the closing sentence of the proof: each $R_rA_a$ is a multiple of the identity on $\mathcal C$ and $\mathcal O$ annihilates the corrupted code, so by Theorem 3.1 the recovery corrects $\mathcal A$.
--
--   Differences from the source:
--   - encoding: an $n$-dimensional Hilbert space $\mathcal H$ and linear operators on it → `EuclideanSpace ℂ ι` for a finite type `ι`, operators `Matrix ι ι ℂ` acting by `QAlgorithms.act`; reason: Lean convention; every $n$-dimensional Hilbert space is isometric to $\mathbb C^n$, so the instances are the same
--   - encoding: an orthonormal basis $|i_L\rangle$ of $\mathcal C$ containing $|0_L\rangle$ → an orthonormal family `e : κ → H` (κ finite) spanning `C`, and an index `i₀ : κ`; reason: an orthonormal family spanning $\mathcal C$ is an orthonormal basis; `i₀` names $|0_L\rangle$
--   - encoding: the construction: $U_i$, the basis $|\nu^0_r\rangle$ of $\mathcal V^0$, $|\nu^i_r\rangle=U_i|\nu^0_r\rangle$, $V_r$ of (21), $R_r$ of (23), $\mathcal O$ → hypotheses `hU`, `hν₀`, `hν₀span`, `hV`, `hRr`, `hO`, with $|\nu^i_r\rangle$ written `act (U i) (ν₀ r)` and `ν₀ : ρ → H` for a finite type `ρ`; reason: these are exactly the properties the paper gives the objects it constructs; the statement is the computation (24)–(25) made from them
--   - encoding: $\mathcal O$, the projection onto the orthogonal complement of $\bigoplus_i\mathcal V^i$ → `O = 1 - ∑ i, ∑ r, |ν^i_r⟩⟨ν^i_r|`; reason: under (20) the $|\nu^i_r\rangle$ form an orthonormal basis of $\bigoplus_i\mathcal V^i$, so this is that projection
--   - encoding: $|x\rangle\langle y|$ → `Matrix.vecMulVec x (star y)` on coordinate vectors; reason: its $(k,l)$ entry is $x_k\bar y_l$, the matrix of $|x\rangle\langle y|$
--   - encoding: $\beta^0_{ar}$, defined by the expansion $A_a|0_L\rangle=\sum_r\beta^0_{ar}|\nu^0_r\rangle$ → `inner ℂ (ν₀ r) (act (A a) (e i₀))`; reason: the coefficient of a vector of $\mathcal V^0$ in the orthonormal basis $|\nu^0_r\rangle$
--   - encoding: "$\mathcal O$ is null on all $A_a|j_L\rangle$" → `∀ a, ∀ ψ ∈ C, act (O * A a) ψ = 0`; reason: equivalent by linearity, since the $|j_L\rangle$ span $\mathcal C$
-- source:
--   Knill, Laflamme, A Theory of Quantum Error-Correcting Codes, arXiv:quant-ph/9604034v1, proof of Theorem 3.2, Eqs.(21)–(25), pp.14–15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
open scoped Matrix

namespace KnillLaflammeQEC

/-- Knill, Laflamme, *A Theory of Quantum Error-Correcting Codes*, arXiv:quant-ph/9604034v1,
proof of Theorem 3.2, Eqs.(21)–(25), pp.14–15: the recovery operator of Eqs.(22)–(23) corrects.
Let `|i_L⟩` be an orthonormal basis of `C` with a distinguished element `|0_L⟩`, `U_i` unitaries
with `U_i A_a|0_L⟩ = A_a|i_L⟩` for all `a`, `|ν⁰_r⟩` an orthonormal basis of
`V⁰ = span{A_a|0_L⟩}`, `|ν^i_r⟩ = U_i|ν⁰_r⟩`, and `V_r` unitaries with `V_r|ν^i_r⟩ = |i_L⟩`
(Eq.(21)), and assume condition (20), `⟨i_L|A_a† A_b|j_L⟩ = 0` for `i ≠ j` (which makes the
`|ν^i_r⟩` mutually orthonormal). With `R_r = V_r Σ_i |ν^i_r⟩⟨ν^i_r|` (Eq.(23)) and `O` the
projection onto the orthogonal complement of `⊕_i V^i`: for every `Ψ ∈ C`,
(a) `R_r A_a|Ψ⟩ = β⁰_ar |Ψ⟩` with `β⁰_ar = ⟨ν⁰_r|A_a|0_L⟩` (Eqs.(24)–(25)), and
(b) `O A_a|Ψ⟩ = 0` ("O is null on all `A_a|j_L⟩`").

**Formalization Note.** `H = EuclideanSpace ℂ ι`, operators `Matrix ι ι ℂ` acting by
`QAlgorithms.act`, unitaries in `Matrix.unitaryGroup ι ℂ`. The basis is an orthonormal family
`e : κ → H` (κ finite) spanning `C`, `i₀ : κ` is the index of `|0_L⟩`; `ν₀ : ρ → H` (ρ finite) is
an orthonormal basis of `V⁰`; `|ν^i_r⟩` is `act (U i) (ν₀ r)`. The rank-one operator `|x⟩⟨y|`
is `Matrix.vecMulVec x (star y)` on coordinate vectors (`(|x⟩⟨y|)_{kl} = x_k ȳ_l`). `O` is
written as `I − Σ_{i,r} |ν^i_r⟩⟨ν^i_r|`, which under the hypotheses is the projection onto the orthogonal
complement of the span of the orthonormal family `{|ν^i_r⟩}`, i.e. of `⊕_i V^i`. The coefficient `β⁰_ar` of the
expansion `A_a|0_L⟩ = Σ_r β⁰_ar|ν⁰_r⟩` is `⟨ν⁰_r|A_a|0_L⟩`. -/
theorem eq_24_25 {ι κ ρ α : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype ρ]
    (C : Submodule ℂ (EuclideanSpace ℂ ι)) (A : α → Matrix ι ι ℂ)
    (e : κ → EuclideanSpace ℂ ι) (he : Orthonormal ℂ e)
    (hspan : Submodule.span ℂ (Set.range e) = C) (i₀ : κ)
    (U : κ → Matrix.unitaryGroup ι ℂ)
    (hU : ∀ (i : κ) (a : α),
      QAlgorithms.act (U i : Matrix ι ι ℂ) (QAlgorithms.act (A a) (e i₀)) =
        QAlgorithms.act (A a) (e i))
    (ν₀ : ρ → EuclideanSpace ℂ ι) (hν₀ : Orthonormal ℂ ν₀)
    (hν₀span : Submodule.span ℂ (Set.range ν₀) =
      Submodule.span ℂ (Set.range fun a => QAlgorithms.act (A a) (e i₀)))
    (h20 : ∀ i j : κ, i ≠ j → ∀ a b : α,
      inner ℂ (e i) (QAlgorithms.act ((A a)ᴴ * A b) (e j)) = 0)
    (V : ρ → Matrix.unitaryGroup ι ℂ)
    (hV : ∀ (i : κ) (r : ρ),
      QAlgorithms.act (V r : Matrix ι ι ℂ) (QAlgorithms.act (U i : Matrix ι ι ℂ) (ν₀ r)) = e i)
    (Rr : ρ → Matrix ι ι ℂ)
    (hRr : ∀ r, Rr r = (V r : Matrix ι ι ℂ) * ∑ i, Matrix.vecMulVec
      (WithLp.ofLp (QAlgorithms.act (U i : Matrix ι ι ℂ) (ν₀ r)))
      (star (WithLp.ofLp (QAlgorithms.act (U i : Matrix ι ι ℂ) (ν₀ r)))))
    (O : Matrix ι ι ℂ)
    (hO : O = 1 - ∑ i, ∑ r, Matrix.vecMulVec
      (WithLp.ofLp (QAlgorithms.act (U i : Matrix ι ι ℂ) (ν₀ r)))
      (star (WithLp.ofLp (QAlgorithms.act (U i : Matrix ι ι ℂ) (ν₀ r))))) :
    (∀ (a : α) (r : ρ), ∀ ψ ∈ C,
      QAlgorithms.act (Rr r * A a) ψ = inner ℂ (ν₀ r) (QAlgorithms.act (A a) (e i₀)) • ψ) ∧
      (∀ a : α, ∀ ψ ∈ C, QAlgorithms.act (O * A a) ψ = 0) := by sorry

end KnillLaflammeQEC
