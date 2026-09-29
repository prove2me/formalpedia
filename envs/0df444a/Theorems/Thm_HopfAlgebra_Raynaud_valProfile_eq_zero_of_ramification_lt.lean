-- Prove2me | Theorems.Thm_HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt
-- name    : HopfAlgebra.Raynaud.valProfile_eq_zero_of_ramification_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/bb0a70ed-0a3e-57cc-85a1-6543aa4af73e
-- title:
--   Nonnegative Raynaud profile with n'≤ e<p-1 vanishes
-- statement:
--   Let $r, p, e$ be natural numbers with $e + 1 < p$, let $n, n' \colon \mathrm{Fin}(r+1) \to \mathbb{N}$ and let $a \colon \mathrm{Fin}(r+1) \to \mathbb{Z}$. Assume the comparison relation $$(n'_i : \mathbb{Z}) = p\,a_i + (n_i : \mathbb{Z}) - a_{i+1} \qquad \text{for all } i \in \mathrm{Fin}(r+1),$$ where $i \mapsto i+1$ is the cyclic successor of the index type $\mathrm{Fin}(r+1)$ (so indices are read modulo $r+1$) and the natural numbers $n_i, n'_i$ are regarded as integers. Assume furthermore that $a_i \ge 0$ for every $i$ and that $n'_i \le e$ for every $i$. Then $a_i = 0$ for every $i$. All data are plain functions on the finite cyclic index set; no Hopf-algebraic or scheme-theoretic structure enters the statement, which is purely an arithmetic assertion about the integer system above. Note that the hypothesis $n'_i \le e$ together with $n'_i \ge 0$ (automatic, $n'$ taking values in $\mathbb{N}$) is what is used, in conjunction with $e + 1 < p$, i.e. $e < p - 1$.
--
--   This is the numerical heart of Raynaud's comparison of two prolongations of a finite flat group scheme of type $(p,\dots,p)$: with equations $X_i^p = \delta_i X_{i+1}$, $n_i = v(\delta_i)$, a second prolongation given by $X'_i = \alpha_i X_i$ has $n'_i = p\,a_i + n_i - a_{i+1}$ with $a_i = v(\alpha_i)$, domination corresponding to $a_i \ge 0$; the conclusion says that in absolute ramification $e < p-1$ the two prolongations coincide. It is used in the proof of [`HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem`](thm.html#HopfAlgebra.FVect.hopfOrder_eq_of_le_of_forall_act_mem).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_Raynaud_valProfile_eq_zero_of_ramification_lt.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HopfAlgebra.Raynaud.valProfile_eq_zero_of_ramification_lt
    {r p e : ℕ} (hpe : e + 1 < p)
    {n n' : Fin (r + 1) → ℕ} {a : Fin (r + 1) → ℤ}
    (hprof : ∀ i : Fin (r + 1), (n' i : ℤ) = p * a i + (n i : ℤ) - a (i + 1))
    (hpos : ∀ i, 0 ≤ a i) (hbound : ∀ i, n' i ≤ e) :
    ∀ i, a i = 0 := by sorry
