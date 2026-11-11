-- Prove2me | Theorems.Thm_OptimalXOR_Total_theorem_1_3
-- name    : OptimalXOR.Total.theorem_1_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:48.300205+00:00
-- url     : https://prove2.me/theorems/346ff127-9d26-4bb1-9706-bb45a14f8d9e
-- title:
--   Theorem 1.3 (XOR lemma) — $c\,n\,\mathrm{IC}_{1/(3n)}(F)\le\mathrm{IC}_{1/3}(F^{\oplus n})\le n\,\mathrm{IC}_{1/(3n)}(F)$ for every total $F$ that is not XOR-reducible
-- statement:
--   Two parties, Alice with $x\in\mathcal X$ and Bob with $y\in\mathcal Y$ ($\mathcal X,\mathcal Y$ finite nonempty sets), communicate by a randomized protocol $\pi$ with public and private randomness whose output is a function of the public randomness and the transcript. The **information complexity** $\mathrm{IC}_\varepsilon(F)$ of a problem $F$ is the infimum, over protocols $\pi$ that err with probability at most $\varepsilon$ on every input, of $\sup_\mu\big(I(M;X\mid Y,R)+I(M;Y\mid X,R)\big)$, the internal information cost in bits, maximized over input distributions $\mu$. For $F:\mathcal X\times\mathcal Y\to\{-1,1\}$ the XOR power is $F^{\oplus n}(x,y)=\prod_{i=1}^nF(x_i,y_i)$ on $\mathcal X^n\times\mathcal Y^n$, and $F$ is **XOR-reducible** if $F(x,y)=a(x)b(y)$ for some $a:\mathcal X\to\{-1,1\}$, $b:\mathcal Y\to\{-1,1\}$.
--
--   **Theorem.** There is a universal constant $c>0$ such that for all finite nonempty $\mathcal X,\mathcal Y$, every communication problem $F:\mathcal X\times\mathcal Y\to\{-1,1\}$ that is not XOR-reducible, and every integer $n\ge1$,
--   $$c\,n\,\mathrm{IC}_{1/(3n)}(F)\le\mathrm{IC}_{1/3}(F^{\oplus n})\le n\,\mathrm{IC}_{1/(3n)}(F).\tag{1.4}$$
--   The constant $c$ is fixed before $\mathcal X$, $\mathcal Y$, $F$ and $n$.
--
--   Running a protocol of error $1/(3n)$ on each copy shows the upper bound; the theorem says this obvious protocol is optimal up to a constant factor, with no additive loss and no dependence on the input length. For XOR-reducible functions the lower bound fails.
--
--   Differences from the source:
--   - encoding: total F : X × Y → {−1, 1} → F : X → Y → ℤˣ, used as the problem total F = fun x y => some (F x y); reason: Lean convention; dom (total F) = X × Y
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: c n IC_{1/(3n)}(F) with c > 0 real → ENNReal.ofReal c * n * IC (total F) (1/(3n)) in ℝ≥0∞, with ∃ c : ℝ, 0 < c placed before ∀ X Y F n; reason: the universal constant is uniform in X, Y, F and n, as in the paper
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 3 (PDF 5), Theorem 1.3, (1.4); restated and proved p. 30 (PDF 32)

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Theorem 1.3 (XOR lemma), p. 3 (restated and proved p. 30). There is a universal constant
`c > 0` such that for every communication problem `F : X × Y → {−1, 1}` that is not
XOR-reducible, and for every integer `n ≥ 1`,
`c n IC_{1/(3n)}(F) ≤ IC_{1/3}(F^{⊕n}) ≤ n IC_{1/(3n)}(F)` (1.4). -/
theorem theorem_1_3 :
    ∃ c : ℝ, 0 < c ∧
      ∀ (X Y : Type) [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y] (F : X → Y → ℤˣ),
        ¬ XORReducible F → ∀ n : ℕ, 1 ≤ n →
          ENNReal.ofReal c * n * IC (total F) (1 / (3 * n)) ≤
              IC (xorPow (total F) n) (1 / 3) ∧
            IC (xorPow (total F) n) (1 / 3) ≤ n * IC (total F) (1 / (3 * n)) := by sorry

end OptimalXOR.Total
