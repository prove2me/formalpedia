-- Prove2me | Theorems.Thm_OptimalXOR_Total_corollary_B_2
-- name    : OptimalXOR.Total.corollary_B_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:07:40.080262+00:00
-- url     : https://prove2.me/theorems/ff2c1320-9dcc-4ddb-9c53-662408f8cc8a
-- title:
--   Corollary B.2 — $\mathrm{IC}_\varepsilon(\mathrm{IP}_n)\ge\frac{(1-2\varepsilon)(1-h_2(\varepsilon))}{16}\,n$
-- statement:
--   Throughout, $\mathcal X,\mathcal Y$ are finite nonempty sets, protocols use public and private randomness and output a function of the public randomness and the transcript, and $\mathrm{IC}_\varepsilon(F)$ is the worst-case information complexity (2.9).
--
--   Let $n\ge1$ be an integer, and let $\mathrm{IP}_n:\{0,1\}^n\times\{0,1\}^n\to\{-1,1\}$ be the inner product function, $\mathrm{IP}_n(x,y)=(-1)^{\sum_{i=1}^nx_iy_i}$. Then for every $0\le\varepsilon<1/2$,
--   $$\mathrm{IC}_\varepsilon(\mathrm{IP}_n)\ge\frac{(1-2\varepsilon)\big(1-h_2(\varepsilon)\big)}{16}\,n,$$
--   where $h_2$ is the binary entropy in bits.
--
--   A linear lower bound on the information complexity of inner product at every error below $1/2$; it supplies the linear lower bound for XOR powers of functions that are not XOR-reducible.
--
--   Differences from the source:
--   - encoding: all sets finite and nonempty (standing assumption, p. 12) → [Fintype X] [Nonempty X] [Fintype Y] [Nonempty Y]; reason: the standing assumption made explicit
--   - reading: protocol with public and private randomness, no restriction on the number of rounds (p. 13) → the published CaiZhuInfo.Matrix.Protocol: a finite binary tree with a fixed speaker per node, one bit per message, tapes arbitrary probability spaces, message maps measurable in the tapes; reason: 'no restriction on the number of rounds' read as unbounded but finite; multi-bit messages are sent bit by bit, which preserves transcripts and information
--   - encoding: the output is a function of the public randomness and the transcript (p. 13) → Protocol.TranscriptDetermined: for every input, Bob's output equals almost surely a measurable function of (public tape, message history); imposed on every protocol in IC_ε, IC_ε(F, µ) and on every protocol the statement quantifies over; reason: the published form of the paper's output convention
--   - encoding: information complexities are nonnegative reals (infimum over protocols, supremum over P(dom F)) → values in ℝ≥0∞: IC(π, µ) enters as ENNReal.ofReal of the published real information cost; inf ∅ = ∞; errors are reals; reason: no junk values for sup/inf; same numbers whenever the paper's quantities are defined
--   - encoding: information quantities of finite random variables → inputs carry the discrete σ-algebra ⊤ inside the definitions; reason: the paper's inputs are finite; conditioning on Y needs the discrete σ-algebra
--   - encoding: Xⁿ, coordinates 1, …, n → Fin n → X, coordinates 0, …, n−1; reason: Lean convention
--   - encoding: binary entropy h₂ in bits → SelectiveDPT.H2 p = Real.binEntropy p / Real.log 2 (published); reason: Mathlib's binEntropy is in nats; same function on [0, 1]
--   - encoding: IPₙ : {0,1}ⁿ × {0,1}ⁿ → {−1, 1} → innerProduct n : (Fin n → Fin 2) → (Fin n → Fin 2) → ℤˣ, used as total (innerProduct n); reason: Lean convention
--   - encoding: ((1 − 2ε)(1 − h₂(ε))/16) n ≤ IC_ε(IPₙ) → ENNReal.ofReal of the left side; reason: the left side is positive for 0 ≤ ε < 1/2, so ofReal is exact
-- source:
--   Alexander A. Sherstov, Optimal XOR Lemmas for Information Complexity, STOC 2027 submission (manuscript sha256 91f89aba…), p. 55 (PDF 57), Corollary B.2

import Mathlib
import Definitions.Def_CaiZhuInfo_Matrix_Protocol
import Definitions.Def_OptimalXOR_Total_Problems
import Definitions.Def_OptimalXOR_Total_InformationComplexity
import Definitions.Def_SelectiveDPT_H2

open CaiZhuInfo.Matrix
open scoped ENNReal

namespace OptimalXOR.Total

/-- Corollary B.2, p. 55. For every integer `n ≥ 1` and every `0 ≤ ε < 1/2`, the inner product
function `IPₙ(x, y) = (−1)^{∑ᵢ xᵢ yᵢ}` on `{0,1}ⁿ × {0,1}ⁿ` satisfies
`IC_ε(IPₙ) ≥ ((1 − 2ε)(1 − h₂(ε))/16) n`. -/
theorem corollary_B_2 (n : ℕ) (hn : 1 ≤ n) (ε : ℝ) (hε₀ : 0 ≤ ε) (hε₁ : ε < 1 / 2) :
    ENNReal.ofReal ((1 - 2 * ε) * (1 - SelectiveDPT.H2 ε) / 16 * n) ≤
      IC (total (innerProduct n)) ε := by sorry

end OptimalXOR.Total
