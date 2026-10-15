-- Prove2me | Theorems.Thm_OAI_QAC_polynomial_approximation
-- name    : OAI.QAC.polynomial_approximation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:47:09.20947+00:00
-- url     : https://prove2.me/theorems/814485a7-4c5b-49ac-9eb9-aef73bf4d1da
-- title:
--   Low-degree, low-weight polynomials approximating the indicator of $0$ up to $N^b$
-- statement:
--   Let $a,b,u$ be real numbers with $0<a<b$ and $\frac{a+b}2<u$. For a real polynomial $p=\sum_kc_kX^k$ write $\|p\|_N=\sum_k|c_k|N^k$. Then for all sufficiently large natural numbers $N$ there is a polynomial $p\in\mathbb R[X]$ such that
--
--   1. $\deg p\le N^u$;
--   2. $\|p\|_N\le e^{N^u}$;
--   3. $p(0)=1$;
--   4. for every integer $x$ with $1\le x\le\lceil N^b\rceil$,
--   $$
--   |p(x)|\le e^{-N^a}.
--   $$
--
--   Such a polynomial separates the value $0$ from all integers between $1$ and $\lceil N^b\rceil$ up to an error $e^{-N^a}$, with degree only slightly above $N^{(a+b)/2}$ rather than $N^b$. Applied to the mismatch operator of a count $D$, it approximates the zero-mismatch projection $P_D^0$ on the subspace with at most $\lceil N^b\rceil$ mismatches, while the degree bound allows it to be expanded into product projections with support of size at most $N^u$, and the weight bound controls the cost of that expansion.
--
--   **Formalization Note** "For all sufficiently large $N$" is `∀ᶠ N : ℕ in atTop`; $\lceil N^b\rceil$ is `Nat.ceil`, the powers $N^a,N^b,N^u$ are real powers, the degree is `natDegree`, and the weight is `weight N p`. No upper bound on $b$ is assumed (the case $b>1$ is included).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/InformationTheory/QuantumCircuit/Asymptotics.lean#L158-L206

import Mathlib
import Definitions.Def_QACParity
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Basic
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_ProductProjection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Circuit
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Count
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Spectral
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Transition
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Reflection
import Definitions.Def_OAI_InformationTheory_QuantumCircuit_Polynomial

open OAI OAI.QAC
open scoped BigOperators Matrix.Norms.L2Operator
open Polynomial Filter Asymptotics

theorem OAI.QAC.polynomial_approximation {a b u : ℝ} (ha : 0 < a) (hab : a < b)
    (hu : (a + b) / 2 < u) :
    ∀ᶠ N : ℕ in atTop, ∃ p : ℝ[X],
      (p.natDegree : ℝ) ≤ (N : ℝ) ^ u ∧ weight N p ≤ Real.exp ((N : ℝ) ^ u) ∧
      p.eval 0 = 1 ∧ ∀ x : ℕ, 1 ≤ x → x ≤ ⌈(N : ℝ) ^ b⌉₊ →
        |p.eval (x : ℝ)| ≤ Real.exp (-((N : ℝ) ^ a)) := by sorry
