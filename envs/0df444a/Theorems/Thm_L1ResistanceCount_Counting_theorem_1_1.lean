-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_theorem_1_1
-- name    : L1ResistanceCount.Counting.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:09:02.72556+00:00
-- url     : https://prove2.me/theorems/1557d21d-7a28-4ea7-a3a5-50c51077589f
-- title:
--   Theorem 1.1 — approximate weighted spanning-tree counting
-- statement:
--   There is one fixed randomized finite arithmetic program with the following property. For every fixed pair of real exponents $a,b\ge0$, constants $C>0$ and an integer $q\ge0$ exist uniformly over all inputs. Let $G$ be any connected undirected graph with $n$ vertices, $m$ labelled positive-real-weight edges and $w_{\max}/w_{\min}\le n^a$. For $0<\varepsilon\le1/2$, with $n^{-b}\le\varepsilon$ required when $n\ne1$, its actual halting output $\widehat T(G)$ satisfies
--
--   $$\Pr[(1-\varepsilon)T(G)\le\widehat T(G)\le(1+\varepsilon)T(G)]\ge\tfrac23,$$
--   $$\mathbb E[\mathrm{executed\ cost}]\le C\left(m+\frac{n^{3/2}}{\varepsilon}\right)\left(1+\log\left(2+n+m+\varepsilon^{-1}\right)\right)^q.$$
--
--   The probability refers to a measurable event on independent uniform and Gaussian tapes. Nontermination has infinite cost and cannot count as successful output. The tree sum is defined independently of the algorithm and of the determinant. The constants may depend on $a,b$, while the program is chosen before those exponents and all graph inputs. The edgeless singleton remains in the domain; arbitrary common rescaling of positive weights introduces no absolute-size or rationality hypothesis.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
--   - reading: polynomial weight and accuracy regimes with Õ arithmetic time → one finite arithmetic RAM program, chosen before all regime exponents, with uniform C and q for each pair of exponents; reason: this makes the uniform asymptotic and arithmetic-operation conventions explicit; it adds no graph or real-weight restriction
--   - encoding: wmax/wmin in the nontrivial graph domain → the equivalent pairwise ratio inequalities, vacuous on the edgeless singleton; reason: this preserves the empty-tree exact branch without defining a minimum of an empty set
--   - encoding: randomized output and expected running time → a measurable halting-output event and the nonnegative extended expectation of the executed instruction count; reason: all randomness and costs come from the finite program trace; failures and nontermination are not removed
--   - generalization: the polynomial lower accuracy bound stated asymptotically → n = 1 or n^(-b) ≤ ε, with 0 < ε ≤ 1/2 in both cases; reason: the singleton has tree weight one and admits a constant-cost exact branch; every instance of the source polynomial regime still satisfies the disjunction, and no nontrivial input or accuracy is removed
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Theorem 1.1, printed p.2 / PDF p.2; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Graph

namespace L1ResistanceCount.Counting

/-- Li–Yang, STOC 2027 submission #881 (October 2026), Theorem 1.1,
printed/PDF page 2. A single finite program is uniform over all polynomial
weight and accuracy regimes and all positive real weight scales.
Runtime is the extended expectation of the operational execution trace.
The singleton is included for every positive accuracy at most 1/2: its
empty-tree weight is 1, whereas the literal bound 1^(-b) ≤ ε would
otherwise exclude this finite-size base case. -/
theorem theorem_1_1 :
    ∃ P : Program, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      ∃ C : ℝ, 0 < C ∧ ∃ q : ℕ,
        ∀ (n m : ℕ) (G : WeightedGraph n m) (ε : ℝ),
          G.IsConnected → PolynomialWeightRange G a →
          0 < ε → (n = 1 ∨ Real.rpow (n : ℝ) (-b) ≤ ε) → ε ≤ 1 / 2 →
          MeasurableSet {ω | Returns P (graphInput G ε) ω (AccurateCount G ε)} ∧
          (2 / 3 : ENNReal) ≤ successProbability P (graphInput G ε) (AccurateCount G ε) ∧
          expectedCost P (graphInput G ε) ≤ ENNReal.ofReal (countingTimeBound C q n m ε) := by sorry

end L1ResistanceCount.Counting
