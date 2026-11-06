-- Prove2me | Theorems.Thm_MatrixLewis_theorem_3_18
-- name    : MatrixLewis.theorem_3_18
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:14:54.935544+00:00
-- url     : https://prove2.me/theorems/64dd8e08-24d0-4867-b1ab-f16fbdc53a85
-- title:
--   Theorem 3.18 — matrix Lewis domination
-- statement:
--   Throughout, $A_1,\dots,A_m, C$ are real symmetric $n\times n$ matrices, the $A_i$ satisfy Assumption 3.1 (linearly independent, with $\bigcap_i \ker A_i=\{0\}$), and $q>2$ is real; $p=q/(q-2)$ and $p'=q/2$.
--
--   Let $S\succ0$ and $\beta:=2n^{2/(q+2)}$. For every $X\in\mathcal L_S=\operatorname{span}\{B_1(S),\dots,B_m(S)\}$,
--   $$
--   \|X\|_{\mathrm{op}}^2\le n^{2/(q+2)}\operatorname{tr}(XW_SX)\le2n^{2/(q+2)}\operatorname{tr}(X\Lambda_SX),
--   \qquad
--   \|X\|_{\mathrm{op}}^2\le\beta\,Q_S\bigl(S^{1/2}XS^{1/2}\bigr).
--   $$
--   Moreover $\beta\ge2$ (for $n\ge1$), $\beta<2e^2$ when $q\ge\log n$, and $\beta=O(1)$ when $q=\Omega(\log n)$: for every $c>0$ there is $C$ with $2n^{2/(q+2)}\le C$ whenever $q>2$ and $q\ge c\log n$.
--
--   Domination bounds operator norms of directions in the span by the local norm.
--
--   Differences from the source:
--   - encoding: β ≥ 2 (the proof's "as n ≥ 1") → 1 ≤ n → 2 ≤ β; reason: at n = 0, 0^{2/(q+2)} = 0; n = 0 is the empty instance
--   - generalization: β = O(1) when q = Ω(log n), for the order n of the slack matrices → ∀ c > 0, ∃ C, ∀ n q, 2 < q → c log n ≤ q → 2n^{2/(q+2)} ≤ C, for every natural n; reason: the clause involves only n and q; every order of slack matrices is a natural number
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Theorem 3.18, pp.28–29, eqs. (41)–(42)

import Mathlib
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_localNormSq
import Definitions.Def_LiqPremiaEq_opNorm

namespace MatrixLewis

/-- **Theorem 3.18** (Matrix Lewis domination; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), pp.28–29, eqs. (41)–(42)). Let `S ≻ 0`.
For every `X ∈ 𝓛_S`, `‖X‖²_op ≤ n^{2/(q+2)} tr(XW_SX) ≤ 2n^{2/(q+2)} tr(XΛ_SX)` and
`‖X‖²_op ≤ βQ_S(S^{1/2}XS^{1/2})`, `β := 2n^{2/(q+2)}`. Moreover, `β ≥ 2`, `β < 2e²` when
`q ≥ log n`, and `β = O(1)` when `q = Ω(log n)`.

**Formalization Note** `‖·‖_op` is the published `LiqPremiaEq.opNorm` (the ℓ² operator norm of a real matrix). `𝓛_S = span{B₁(S), …, B_m(S)}`. "β ≥ 2" is stated for `n ≥ 1` (the
paper's "as n ≥ 1", p.29; at `n = 0`, `0^{2/(q+2)} = 0`). "β = O(1) when q = Ω(log n)": for every
`c > 0` there is `C` with `2n^{2/(q+2)} ≤ C` for all `n` and all `q > 2` with `q ≥ c log n`.
`log` is natural. Standing assumptions of §3 are hypotheses. -/
theorem theorem_3_18 {n m : ℕ} (q : ℝ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ i, (A i).IsHermitian) (h31 : Assumption31 A) (hq : 2 < q) :
    let β : ℝ := 2 * (n : ℝ) ^ (2 / (q + 2))
    (∀ S : Matrix (Fin n) (Fin n) ℝ, S.PosDef →
      ∀ X ∈ Submodule.span ℝ (Set.range (scaled A S)),
        LiqPremiaEq.opNorm X ^ 2 ≤ (n : ℝ) ^ (2 / (q + 2)) * (X * rightWeight q A S * X).trace ∧
        (n : ℝ) ^ (2 / (q + 2)) * (X * rightWeight q A S * X).trace ≤
          2 * (n : ℝ) ^ (2 / (q + 2)) * (X * lewisWeight q A S * X).trace ∧
        LiqPremiaEq.opNorm X ^ 2 ≤ β * localNormSq q A S (mpow (1 / 2 : ℝ) S * X * mpow (1 / 2 : ℝ) S)) ∧
    (1 ≤ n → 2 ≤ β) ∧
    (Real.log n ≤ q → β < 2 * Real.exp 2) ∧
    (∀ c : ℝ, 0 < c → ∃ Cβ : ℝ, ∀ (n' : ℕ) (q' : ℝ), 2 < q' → c * Real.log n' ≤ q' →
      2 * (n' : ℝ) ^ (2 / (q' + 2)) ≤ Cβ) := by sorry

end MatrixLewis
