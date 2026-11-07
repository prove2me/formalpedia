-- Prove2me | Theorems.Thm_LinSysAmp_proposition_4_8
-- name    : LinSysAmp.proposition_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:58:22.019112+00:00
-- url     : https://prove2.me/theorems/23ac8342-a98f-4c36-a8e9-5e7c76c38d51
-- title:
--   Proposition 4.8 — amplification with updates of rank $k$
-- statement:
--   Let $F$ be a finite field with $q$ elements, let $\omega$ be the exponent of matrix multiplication over $F$, and let $\varepsilon>0$. There are a single program $P$ of the field-operation machine and a constant $C>0$ such that the following holds for all integers $1\le k\le n$, all reals $\alpha>0$ and $0<\delta<1/2$, and every oracle $\mathcal O$ for $n\times n$ systems. Put
--   $$
--   t=\bigl\lceil8\alpha^{-1}\log(1/\delta)\bigr\rceil,
--   $$
--   where $\log$ is the natural logarithm, and give $P$ the input $(n,k,t,M,y)$.
--
--   1. For all $M\in\mathrm{GL}_n(F)$ and $y\in F^n$, every run halts having made at most $t$ oracle calls and at most $C\,t\,n^2k^{\omega-2+\varepsilon}$ field operations.
--   2. For all $M\in\mathrm{GL}_n(F)$ and $y\in F^n$, $P$ never outputs a wrong solution: any vector it outputs equals $M^{-1}y$.
--   3. If $\mathcal O$ solves $\mathsf{LINEQ}_{n,q}$ with probability at least $\alpha$, then
--   $$
--   \Pr_{M\leftarrow\mathrm{GL}_n(F)}\Bigl[\forall y\in F^n:\ \Pr_{P}\bigl[P(M,y)=M^{-1}y\bigr]\ge1-\delta\Bigr]\ge1-\frac{64}{\alpha q^{2k}}.
--   $$
--
--   The theorem turns any algorithm that solves a random invertible linear system with small probability $\alpha$ into a solver that works on every right-hand side of almost every invertible matrix. The number of calls does not depend on the exceptional fraction, and the running time grows only linearly in $1/\alpha$. For a time-$T$ oracle, clause 1 gives total time at most $t\,(T+C\,n^2k^{\omega-2+\varepsilon})$. Since $\alpha\le1$ under the hypothesis and $\delta<1/2$, we have $t\le(8+1/\log2)\,\alpha^{-1}\log(1/\delta)$, which yields the printed bound $O((T+n^2k^{\omega-2+o(1)})\alpha^{-1}\log(1/\delta))$.
--
--   **Formalization Note** The program is chosen before $n,k,\alpha,\delta$ and the oracle, so it is a black-box reduction, and it receives $t$ as an input. The paper assumes that $\alpha$ is known and takes $t$ as a parameter of the algorithm. Clauses 1 and 2 hold for every oracle. Clause 3 reads the probability that the run has halted with output $M^{-1}y$ after a number of steps $N$ past the halting bound.
--
--   Differences from the source:
--   - reading: "there is an algorithm" in a model that lists operations but names no machine → a program of `LinSysAmp.Machine` (unit-cost field and index instructions, an oracle instruction); reason: §3.1 gives the operations, not a machine; every listed operation is one instruction and nothing else is free
--   - reading: O(… n²k^{ω−2+o(1)} …) with ω "over the field under consideration" → ∀F, ∀ε>0, ∃P, ∃C; the constant and the program depend on F and ε only; reason: ω is an infimum over a field, need not be attained, and depends on the field; the page's proof applies k^{ω+o(1)} in this sense
--   - reading: ω, "the exponent of matrix multiplication over the field under consideration" (§3.2) → `omegaAlg F`, whose programs compute the product as polynomials, not the published `omega F`, whose programs need only be correct as functions on the finite field; reason: the standard algebraic exponent; a time bound in the function-level exponent is not known to follow from the page's argument, because recursive block multiplication needs a polynomial identity
--   - generalization: for each O, k, δ there is an algorithm B_k → one program for all n, k, α, δ and O, which reads n, k, t from its input; reason: the printed statement follows by fixing those values, and the paper's algorithms are uniform and use O as a black box
--   - generalization: O is a time-T algorithm; time O((T + n²k^{ω−2+o(1)})α⁻¹log(1/δ)) → O is any randomized map; calls ≤ t and ops ≤ C·t·n²·k^{ω−2+ε} on every run; reason: a time-T algorithm is such a map, and total time ≤ ops + T·calls with t ≤ (8 + 1/log 2)α⁻¹log(1/δ) gives the printed bound
--   - generalization: the first two bullets, under the standing hypothesis that O solves LINEQ with probability ≥ α → clauses 1 and 2 for every oracle, with no success hypothesis; reason: the page's proof does not use the hypothesis for them; the printed case is a special case
--   - reading: "We assume that the success probability α of the oracle is known" (p.19); Figure 3 has parameter t → t = ⌈8α⁻¹log(1/δ)⌉ is an input of the program; reason: this is the way the paper uses α; the program never sees α or δ otherwise
--   - encoding: Pr over M ← GL_n(F_q); Pr over the coins of B_k → a normalized count over `InvMat n F`; the mass of runs halted with output M⁻¹y after N steps; reason: N exceeds every running time allowed by clause 1, so this is the eventual output law
--   - encoding: "halts within T steps on every input" (§3.1) and "never outputs a wrong solution" → clauses 1 and 2 for every input (M, y) with M ∈ GL_n(F_q); reason: the inputs of LINEQ_{n,q} (Definition 3.1) are pairs with M invertible, and M⁻¹y is undefined otherwise
-- source:
--   Couteau, Melissaris, Radhika Sajith, Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography, arXiv:2611.04680 (version held, sha256 af7a90ac…), Proposition 4.8, p.21 (PDF p.23)

import Mathlib
import Definitions.Def_LinSysAmp_omegaAlg
import Definitions.Def_LinSysAmp_Machine
import Definitions.Def_LinSysAmp_lineqSuccess

set_option autoImplicit false

open Matrix

namespace LinSysAmp

/-- Proposition 4.8 (Amplification with updates of rank k), p.21 (PDF p.23). Couteau, Melissaris,
Radhika Sajith, *Hardness Self-Amplification in Linear Algebra and Fine-Grained Cryptography*,
arXiv:2611.04680 (version held, sha256 af7a90ac…).

"Let O be a time-T algorithm that solves LINEQ_{n,q} with probability at least α > 0. For all
1 ≤ k ≤ n and 0 < δ < 1/2, there is an algorithm B_k with the following properties.
• B_k makes at most t = ⌈8α⁻¹ log(1/δ)⌉ calls to O, and runs in time
O((T + n²k^{ω−2+o(1)})α⁻¹ log(1/δ)).
• B_k never outputs a wrong solution.
• For all but a 64q^{−2k}/α fraction of the matrices, B_k succeeds with probability 1 − δ on every
right-hand side: Pr_{M←GL_n(F_q)}[∀y ∈ F_qⁿ : Pr_{B_k}[B_k(M, y) = M⁻¹y] ≥ 1 − δ] ≥ 1 − 64/(αq^{2k})."

**Formalization Note.**
* *Algorithm.* "There is an algorithm" is a program `P` of the field-operation machine
  `LinSysAmp.Machine` (§3.1's model: unit-cost `+ − × ⁻¹`, comparison, uniform sampling, memory
  access; costed index arithmetic without multiplication; the oracle reached only through `query`,
  with fresh randomness per call). The program is chosen for the field `F` and the slack `ε` only,
  before `n, k, α, δ` and the oracle: it reads `n, k` and the number of attempts `t` from its input
  (`initConfig`; "we assume that the success probability α of the oracle is known", p.19, and
  Figure 3 takes `t` as a parameter). It is a black-box reduction: the same program works for every
  oracle `O`.
* *Oracle.* `O` is any randomized map `Oracle n F`. A time-`T` algorithm is one; `T` enters only
  through the total time `ops + T·calls`, so the statement counts the calls instead of fixing `T`.
* *Time.* On every run (every configuration in the support, for every oracle and every input with
  `M` invertible), the program halts within `N = t + ⌈B⌉ + 1` steps with `calls ≤ t` and
  `ops ≤ B = C·t·n²·k^{ω−2+ε}`, where `ω = omegaAlg F` is the matrix multiplication exponent over the
  same field (§3.2). With a time-`T` oracle the total time is
  at most `t·(T + C n² k^{ω−2+ε})`, and `t ≤ (8 + 1/log 2)α⁻¹ log(1/δ)` for `α ≤ 1`, so this implies
  the printed `O((T + n²k^{ω−2+o(1)})α⁻¹ log(1/δ))` with `o(1)` read as "for every `ε > 0`, with a
  constant depending on `F` and `ε`". (Every running step adds exactly `1` to `ops + calls`, so
  halting by step `N` is no extra condition.)
* *Never wrong.* Every halted run that outputs a vector outputs `M⁻¹y`, for every oracle.
* *Success.* "Solves LINEQ with probability α" is `α ≤ lineqSuccess O` (Definition 3.1, over
  `M ← GL_n(F)` and `y ← Fⁿ`). `Pr_{B_k}[B_k(M, y) = M⁻¹y]` is `outputProb`, the probability that the
  run has halted with output `M⁻¹y` after `N` steps. `Pr_{M ← GL_n(F_q)}` is a normalized count over
  `InvMat n F`. `log` is the natural logarithm (§3.1), `⌈·⌉` is `Nat.ceil`, `q = Fintype.card F`. -/
theorem proposition_4_8 (F : Type*) [Field F] [Fintype F] [DecidableEq F] (ε : ℝ) (hε : 0 < ε) :
    ∃ P : Program F, ∃ C : ℝ, 0 < C ∧
      ∀ (n k : ℕ), 1 ≤ k → k ≤ n → ∀ (α δ : ℝ), 0 < α → 0 < δ → δ < 1 / 2 →
      ∀ O : Oracle n F,
        let t : ℕ := ⌈8 / α * Real.log (1 / δ)⌉₊
        let B : ℝ := C * t * (n : ℝ) ^ 2 *
          (k : ℝ) ^ (omegaAlg F - 2 + ε)
        let N : ℕ := t + ⌈B⌉₊ + 1
        (∀ (M : InvMat n F) (y : Fin n → F), HaltsWithin n O P (initConfig n k t M.1 y) N t B) ∧
        (∀ (M : InvMat n F) (y : Fin n → F), ∀ σ ∈ (run n O P N (initConfig n k t M.1 y)).support,
          ∀ w : Fin n → F, σ.status = .done (some w) → w = M.1⁻¹ *ᵥ y) ∧
        (α ≤ lineqSuccess O →
          1 - 64 / (α * (Fintype.card F : ℝ) ^ (2 * k)) ≤
            ((Finset.univ.filter fun M : InvMat n F => ∀ y : Fin n → F,
                1 - δ ≤ outputProb n O P (initConfig n k t M.1 y) N (M.1⁻¹ *ᵥ y)).card : ℝ) /
              (Fintype.card (InvMat n F) : ℝ)) := by sorry

end LinSysAmp
