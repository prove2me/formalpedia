-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_SampleGraph_exists_avoiding
-- name    : OAI.TorsionFreeZeroDivisors.SampleGraph.exists_avoiding
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:13:30.158415+00:00
-- url     : https://prove2.me/theorems/8fa825e2-db19-4cfa-b4a3-0e05efe3abcf
-- title:
--   Propositions 3.1 and 4.5 (OpenAI) — for large $n$ there are samples with the diameter bound and no bounded nearly-paired path system
-- statement:
--   Let $B,K,I$ be natural numbers with $K,I>0$. For every sufficiently large level $n$, every vertex $x$ of side $A$ and every vertex $y$ of side $B$, there is a pair $r=(r_A,r_B)$ of girth-conditioned matchings, $r\in\mathcal S(n)$, such that
--
--   1. every connected component of both vertex graphs has diameter at most $D_0L$ (the diameter event of Lemma 2.3), and
--   2. the sampled graph $\Gamma=\Gamma_A\sqcup\Gamma_B$ carries no bounded system with parameters $(B,K,I)$ rooted at $x,y$.
--
--   A bounded system is a family of at most $K$ nonempty non-backtracking dart sequences in $\Gamma$, all cyclically non-backtracking except possibly one root path that starts at $x$ or $y$, with total length $\Sigma$ between $L$ and $BL$. Its positions are paired by at most $I$ interval comparisons (order-preserving with equal letters, or order-reversing with inverse letters). Paired positions carry darts on distinct undirected edges, and at most $\varepsilon\Sigma$ positions are unpaired, with $\varepsilon=1/2467200$ fixed in advance:
--
--   $$\exists N\ \forall n\ge N\ \forall x\,\forall y\ \exists r\in\mathcal S(n):\ \mathrm{Diam}(n,r)\ \wedge\ \mathrm{BoundedSystem}(B,K,I,n,r,x,y)=\varnothing .$$
--
--   This is the existence of good samples that Proposition 4.5 uses. It combines the girth conditioning of Lemma 2.2, the diameter bound of Lemma 2.3 (`OAI.TorsionFreeZeroDivisors.TypedDiameter.diameter_tendsto`) and the bounded-pattern estimate of Proposition 3.1 (`OAI.TorsionFreeZeroDivisors.BoundedPattern.probability_union`).
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 7: “Proposition 3.1 (Bounded-pattern estimate). There is a constant $\varepsilon > 0$, depending only on the fixed types and turn weights, with the following property. For every fixed positive integer $K$, fixed real $C \ge 1$, and fixed nonnegative integer $I$, the conditional probability tends to zero that there exists a system as above having at most $K$ paths, total length $H$ with $L \le H \le CL$, at most $I$ interval pairs, and $b$ unpaired occurrences, where $b \le \varepsilon H$.” And p. 18, Proposition 4.5: “In particular, for all sufficiently large admissible $n$ there exist graphs of the prescribed types, with girth at least $L$ and the diameter bound of Lemma 2.3, admitting no such arrangement.”
--
--   **Formalization note.** The objects are OpenAI's (`ActualPatternEvent.samples`, `GraphSample.Diameters`, `SampleGraph.BoundedSystem`, from the bundle `Def_TorsionFreeZeroDivisorsConstruction`). The conclusion is the existence form of “probability tending to zero”, for every $(B,K,I)$ at once and with $\varepsilon$ explicit. The sample $r$ may depend on $x$ and $y$. The bound $B$ plays the role of $C$. With $B=0$ the condition is vacuous once $L\ge1$. The inversion of letters goes through one fixed, unspecified bijection (`Fintype.equivOfCardEq`); the paper pairs the letters “arbitrarily”.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, pp. 5-7, Lemmas 2.2 and 2.3 and Proposition 3.1, combined into the existence of good samples used by Proposition 4.5 (p. 18); Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), SampleGraph.exists_avoiding

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.SampleGraph

open scoped Classical
open ActualPatternEvent

theorem exists_avoiding (Bnd K I : ℕ) (hK : 0<K) (hI : 0<I) :
    ∀ᶠ rep in Filter.atTop,∀ (x : VA rep) (y : VB rep),
      ∃ r∈samples rep,GraphSample.Diameters rep r ∧
        IsEmpty (BoundedSystem Bnd K I rep r x y) := by
  sorry

end OAI.TorsionFreeZeroDivisors.SampleGraph
