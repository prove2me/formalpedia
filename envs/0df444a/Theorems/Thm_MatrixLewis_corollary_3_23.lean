-- Prove2me | Theorems.Thm_MatrixLewis_corollary_3_23
-- name    : MatrixLewis.corollary_3_23
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:53.926385+00:00
-- url     : https://prove2.me/theorems/0cad27f5-5cc9-4e43-88d1-a871e0be83e0
-- title:
--   Corollary 3.23 — $K_{q,n}^2f_q$ is a self-concordant barrier with parameter $O(mq^2(1+n^{2/(q+2)}))$
-- statement:
--   There are absolute constants $C_{\mathrm{sc}}\ge1$, $C'_{\mathrm{sc}}>0$ and $C_0>0$ such that the following hold. Let $A_1,\dots,A_m,C\in\mathbb S^n$ with the $A_i$ satisfying Assumption 3.1 (linearly independent, $\bigcap_i\ker A_i=\{0\}$), let $q>2$ be real, and let $f_q$ be the matrix Lewis barrier on $\mathcal D=\{x:\sum_ix_iA_i-C\succ0\}$. Put
--   $$
--   K_{q,n}:=C_{\mathrm{sc}}\,q\bigl(1+\sqrt{2n^{2/(q+2)}}\bigr),\qquad K_q:=C'_{\mathrm{sc}}\,q .
--   $$
--
--   1. $K_{q,n}^2f_q$ is a standard self-concordant barrier for $\mathcal D$ with parameter (at most) $K_{q,n}^2m$, and $K_{q,n}^2m\le C_0\,mq^2\bigl(1+n^{2/(q+2)}\bigr)$.
--   2. If also $q\ge\log n$, then $K_q^2f_q$ is a standard self-concordant barrier for $\mathcal D$ with parameter $K_q^2m$, and $K_q^2m\le C_0\,mq^2$.
--   3. For $n\ge3$ and $q=\Theta(\log n)$ — for all $0<c_1\le c_2$ there is $C(c_1,c_2)$ such that, whenever $n\ge3$ and $c_1\log n\le q\le c_2\log n$ — the first parameter is at most $C(c_1,c_2)\,m\log^2n$, and so is the second when also $q\ge\log n$.
--
--   A standard self-concordant barrier $g$ with parameter $\nu$ tends to $+\infty$ at the boundary of $\mathcal D$, is convex and three times continuously differentiable on $\mathcal D$ with $|D^3g(x)[h,h,h]|\le2(D^2g(x)[h,h])^{3/2}$, and satisfies $Dg(x)[h]\le\sqrt{\nu\,D^2g(x)[h,h]}$. At $q=\Theta(\log n)$ the barrier gives path following in $O(\sqrt m\log n\cdot\log(1/\varepsilon))$ iterations.
--
--   **Formalization Note** The barrier property is the published predicate `EntropicBarrier.Universal.IsNuSelfConcordantBarrier` applied to the open set $\mathcal D$.
--
--   Differences from the source:
--   - encoding: standard self-concordant barrier with parameter at most ν [Nes18, Def. 5.1.1, 5.3.2] → EntropicBarrier.Universal.IsNuSelfConcordantBarrier 𝒟 g ν; reason: the predicate is Nesterov's definition with K := 𝒟 open (barrier at the frontier, convex C³ self-concordant, Dg[h] ≤ √(νD²g[h,h])); a parameter at most ν is a parameter ν since the bound is monotone in ν
--   - encoding: O(mq²(1 + n^{2/(q+2)})), O(mq²) → one absolute constant C₀ > 0 quantified first; reason: O(·) hides an absolute constant (p.17)
--   - reading: q = Θ(log n) and the bound O(m log² n) → ∀ 0 < c₁ ≤ c₂, ∃ C(c₁, c₂) for all n ≥ 3 and c₁ log n ≤ q ≤ c₂ log n; reason: the standard meaning of Θ with the O-constant depending on the Θ-constants
--   - generalization: the O(m log² n) clause for the n, m of SDP data satisfying Assumption 3.1 → the same bound for all natural n ≥ 3, m and real q, without data; reason: the clause involves only n, m and q; data instances are among them
--   - encoding: K_{q,n} and K_q built from the constants C_sc and C′_sc of Theorem 3.21 and Corollary 3.22 → C_sc ≥ 1 and C′_sc > 0 existentially quantified first in this statement; reason: those results fix them only as absolute constants, so the claim is the same; a larger C′_sc also works, so positivity is no restriction
-- source:
--   Kelner, Jiang, Sidford, Zhang, Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations, STOC 2027 submission (manuscript sha256 31ce765b…), Corollary 3.23, p.34 (proof pp.34–35)

import Mathlib
import Definitions.Def_EntropicBarrier_Universal_SelfConcordantBarrier
import Definitions.Def_MatrixLewis_Assumption31
import Definitions.Def_MatrixLewis_barrier

namespace MatrixLewis

/-- **Corollary 3.23** (Standard normalization; Kelner–Jiang–Sidford–Zhang, *Matrix Lewis Weights: Solving Semidefinite Programs in Square Root Constraints Iterations*, STOC 2027 submission (manuscript sha256 31ce765b…), p.34). Assume that Assumption 3.1 holds,
and let `q > 2` be real. Then `K²_{q,n} f_q` is a standard self-concordant barrier with parameter
at most `K²_{q,n} m = O(mq²(1 + n^{2/(q+2)}))`. If also `q ≥ log n`, then `K²_q f_q` is one with
parameter at most `K²_q m = O(mq²)`. For `n ≥ 3` and `q = Θ(log n)`, the first bound is
`O(m log² n)`, and so is the second when also `q ≥ log n`.

Here `K_{q,n} = C_sc q(1 + √β)`, `β = 2n^{2/(q+2)}` (Theorem 3.21), and `K_q = C′_sc q`
(Corollary 3.22).

**Formalization Note** The absolute constants `C_sc ≥ 1`, `C′_sc > 0` and `C₀ > 0` (the `O` of the
first two bounds) are quantified first, before `n`, `m`, the data and `q`. "Standard
self-concordant barrier with parameter ν" is the published
`EntropicBarrier.Universal.IsNuSelfConcordantBarrier` on `K := 𝒟` (open): `g → +∞` at every
frontier point of `𝒟` from inside, `g` convex, `C³` and `|D³g[h,h,h]| ≤ 2(D²g[h,h])^{3/2}` on `𝒟`,
and `Dg(x)[h] ≤ √(ν D²g(x)[h,h])`; a parameter at most `ν` is a parameter `ν`. "`q = Θ(log n)`"
reads: for all `0 < c₁ ≤ c₂` there is `C(c₁, c₂)` that works for all `n ≥ 3` and
`c₁ log n ≤ q ≤ c₂ log n`; this arithmetic clause is stated for all `n`, `m`, `q`, without the
data. `log` is natural; `√` is `Real.sqrt`; powers of `n` are `Real.rpow`. -/
theorem corollary_3_23 :
    ∃ Csc : ℝ, 1 ≤ Csc ∧ ∃ C'sc : ℝ, 0 < C'sc ∧ ∃ C₀ : ℝ, 0 < C₀ ∧
      (∀ (n m : ℕ) (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin n) (Fin n) ℝ) (q : ℝ),
        (∀ i, (A i).IsHermitian) → C.IsHermitian → Assumption31 A → 2 < q →
        let K : ℝ := Csc * q * (1 + Real.sqrt (2 * (n : ℝ) ^ (2 / (q + 2))))
        let Kq : ℝ := C'sc * q
        (EntropicBarrier.Universal.IsNuSelfConcordantBarrier (dom A C)
            (fun x => K ^ 2 * barrier q A C x) (K ^ 2 * m) ∧
          K ^ 2 * m ≤ C₀ * m * q ^ 2 * (1 + (n : ℝ) ^ (2 / (q + 2)))) ∧
        (Real.log n ≤ q →
          EntropicBarrier.Universal.IsNuSelfConcordantBarrier (dom A C)
              (fun x => Kq ^ 2 * barrier q A C x) (Kq ^ 2 * m) ∧
            Kq ^ 2 * m ≤ C₀ * m * q ^ 2)) ∧
      (∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ ≤ c₂ → ∃ Cθ : ℝ, ∀ (n m : ℕ) (q : ℝ),
        3 ≤ n → 2 < q → c₁ * Real.log n ≤ q → q ≤ c₂ * Real.log n →
        (Csc * q * (1 + Real.sqrt (2 * (n : ℝ) ^ (2 / (q + 2))))) ^ 2 * m ≤
            Cθ * m * Real.log n ^ 2 ∧
          (Real.log n ≤ q → (C'sc * q) ^ 2 * m ≤ Cθ * m * Real.log n ^ 2)) := by sorry

end MatrixLewis
