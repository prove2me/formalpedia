-- Prove2me | Theorems.Thm_OWFLocalDesc_Supplement_theorem_A_2
-- name    : OWFLocalDesc.Supplement.theorem_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T17:01:04.26606+00:00
-- url     : https://prove2.me/theorems/8fa8a743-cf6f-49eb-a921-8ef3e1dc14c4
-- title:
--   Theorem A.2 — exact recovery of the quantile at a uniformly random grid threshold without one-way functions
-- statement:
--   Assume one-way functions do not exist. Fix a decoder $U$, a polynomial sample-size schedule $m(n)\ge1$, a PAC-style samplable $D=(\mu,Q)$ with concept-seed length $q(n)$ and a coding header $\sigma_Q$ of length $c_Q$, an adequate polynomial clock $t(n)\ge1$, a positive function $p(n)\ge1$ (a positive polynomial in the paper), and a polynomial-time computable integer schedule $P(n)\ge p(n)$. Let
--   $$c'(n)=\lceil\log(m+1)\rceil+c_Q+3,\qquad L(n)=q(n)+c'(n),$$
--   let $G(n)$ be the least power of two with $G(n)\ge 8P(n)(L(n)+1)$, and for $0\le j<G(n)$ let $\theta_j=\frac12+\frac{2j+1}{8G(n)}$.
--
--   Then there is one PPT algorithm $B$ such that, for infinitely many point lengths $n$,
--   $$\Pr_{(x,y)\sim D_n,\ j,\ B}\Big[B(1^n,x,y,j)=\mathrm{pSC}^t_{\theta_j}(x,y)\Big]\ \ge\ 1-\frac1{p(n)} ,$$
--   where the grid index $j$ is uniform on $\{0,\dots,G(n)-1\}$ and independent of the dataset and the coins. The decoder inside every certificate runs for the original $t(n)$ steps.
--
--   Without one-way functions, the quantile is therefore computable exactly, rather than only between two thresholds, once the threshold is drawn at random from an explicit polynomial-size grid.
--
--   Differences from the source:
--   - generalization: one efficiently universal Turing machine U, fixed once and for all (§2.1, p.12) → every `Decoder`: any step-indexed machine with the clock, sequential-reading, universality and simulation properties stated in §2.1; reason: §2.1's machine has these properties, so the statement specializes to it
--   - reading: the coding header σ_Q fixed once and for all for D (Definition 3.2), adequacy relative to it → every header σQ with `IsCodingHeader U D σQ`; reason: the paper fixes the header without naming it; the result is meant for any such choice (as in the published Theorem 5.1)
--   - generalization: a positive polynomial p(n) ≥ 1 and a polynomial-time computable integer polynomial P(n) ≥ p(n) → any real function p with p(n) ≥ 1 and any `QuantumPRC.EffPoly` schedule P : ℕ → ℕ with p(n) ≤ P(n); reason: every positive integer polynomial P is an EffPoly schedule and every positive polynomial p is such a function, so the statement specializes to the source; B depends only on P, and 1 − 1/p ≤ 1 − 1/P
--   - encoding: c_Q the constant of Lemma 3.3 for D; L(n) = q(n) + c′(n); G(n) the least power of two ≥ 8P(n)(L(n)+1); θ_j = 1/2 + (2j+1)/(8G(n)) → c_Q = σQ.length; `priceCutoff`, `gridSize` = 2^{Nat.clog 2 (8P(n)(L(n)+1))}, `gridTheta`; reason: c_Q is the header length (Definition 3.2); 2^{⌈log₂ N⌉} is the least power of two ≥ N
--   - encoding: Pr_{(x,y)∼D_n, j, B}[B(1^n,x,y,j) = pSC^t_{θj}(x,y)] with j uniform and independent → `gridSucc`: (1/G) Σ_j Σ_{x,y} datasetMass · B.prob(gridInput x y j)(decodeOut out = some (toWT (pSC …))); reason: the same probability, with exact equality in Z ∪ {∞}
--   - encoding: polynomial schedules m(n) ≥ 1, t(n) ≥ 1 → `QuantumPRC.EffPoly` schedules with m n ≥ 1, t n ≥ 1; reason: EffPoly is polynomially bounded and polynomial-time computable, exactly the paper's polynomial schedules
--   - encoding: a PPT algorithm receiving 1^n and a dataset (and a tolerance or grid index), whose output is a binary integer or the symbol ∞ (else a failure) → published `PPT` on `datasetCode` (followed by the extra argument in binary); output read by `decodeOut`; reason: the mission's published uniform PPT model and fixed injective codes; no instance changes
--   - encoding: quantiles in Z≥0 ∪ {∞}; closed intervals of Z ∪ {∞} with ∞ ± d = ∞; ⌈log m⌉ → `pSC` in ℕ∞; `InInterval` in `WithTop ℤ`; `Nat.clog 2`; reason: same values and the same order
-- source:
--   Myrisiotis, One-Way Functions and Local Descriptions of Random Data, STOC 2027 submission (held manuscript, sha256 d818fa43…4c4e), Theorem A.2, p.35 (restatement of Theorem 1.7)

import Mathlib
import Definitions.Def_QuantumPRC_IsPolyFamily
import Definitions.Def_OWFLocalDesc_OWFExist
import Definitions.Def_OWFLocalDesc_IsCodingHeader
import Definitions.Def_OWFLocalDesc_Adequate
import Definitions.Def_OWFLocalDesc_Supplement_gridSucc
set_option autoImplicit false

namespace OWFLocalDesc.Supplement

open OWFLocalDesc

/-- **Theorem A.2 (Exact recovery at a random threshold; restatement of Theorem 1.7).**
Myrisiotis, *One-Way Functions and Local Descriptions of Random Data*, STOC 2027 submission
(held manuscript, sha256 d818fa43…4c4e), Theorem A.2, p.35: "Assume one-way functions do not
exist. Fix a polynomial sample-size schedule m(n) ≥ 1, a PAC-style samplable D = (µ,Q), an adequate
polynomial clock t, and a positive polynomial p(n) ≥ 1. Let c′(n) = ⌈log(m+1)⌉ + c_Q + 3, with c_Q
the constant of Lemma 3.3 for D, and let L(n) = q(n) + c′(n) be the resulting integer price
cutoff, as in the proof of Theorem 5.1. Choose a polynomial-time computable integer polynomial
P(n) ≥ p(n), and let G(n) be the least power of two satisfying G(n) ≥ 8P(n)(L(n)+1). For
0 ≤ j < G(n) put θ_j = 1/2 + (2j+1)/(8G(n)). There is one PPT algorithm B = B_{D,t,p,P} such that,
for infinitely many point lengths n, Pr_{(x,y)∼D_n,j,B}[B(1^n,x,y,j) = pSC^t_{θj}(x,y)] ≥ 1 − 1/p(n).
The grid index is uniform on {0,...,G(n)−1} and independent of the dataset and the algorithm's
coins. The decoder inside every certificate is run for the original t(n) steps."

**Formalization Note.**
1. For every decoder `U` and every coding header `σQ` of `D` (adequacy is relative to it);
   `c_Q = σQ.length` (Definition 3.2), so `L(n)` is `priceCutoff D m σQ n`, `G(n)` is
   `gridSize` (`2 ^ ⌈log₂ 8P(n)(L(n)+1)⌉`, the least power of two above that number) and `θ_j` is
   `gridTheta`.
2. `P` is any polynomially bounded, polynomial-time computable schedule (`QuantumPRC.EffPoly`) with
   `p(n) ≤ P(n)`; every integer polynomial `P ≥ p ≥ 1` is one. `p` is any real function with
   `p(n) ≥ 1`; a positive polynomial is one.
3. One algorithm `B` for every grid point, chosen before `n`; it receives `j` in binary
   (`gridInput`). "For infinitely many n" is `∀ N, ∃ n ≥ N`. The event is exact equality with the
   quantile, `∞` included (`gridSucc`). -/
theorem theorem_A_2 (hno : ¬ OWFExist) (U : Decoder) (m : ℕ → ℕ) (hm : QuantumPRC.EffPoly m)
    (hm1 : ∀ n, 1 ≤ m n) (D : PACSampler) (σQ : List Bool) (hσQ : IsCodingHeader U D σQ)
    (t : ℕ → ℕ) (ht : QuantumPRC.EffPoly t) (ht1 : ∀ n, 1 ≤ t n) (hadq : Adequate U D σQ t)
    (p : ℕ → ℝ) (hp : ∀ n, 1 ≤ p n)
    (P : ℕ → ℕ) (hP : QuantumPRC.EffPoly P) (hpP : ∀ n, p n ≤ (P n : ℝ)) :
    ∃ B : PPT, ∀ N : ℕ, ∃ n ≥ N,
      1 - 1 / p n ≤ gridSucc U D t m σQ P B n := by sorry

end OWFLocalDesc.Supplement
