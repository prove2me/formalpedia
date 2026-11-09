-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_2
-- name    : HypercliqueAC0.FixedDepth.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:37.676698+00:00
-- url     : https://prove2.me/theorems/89fce6e8-006b-4116-9d4b-f21b21376c8c
-- title:
--   Lemma 4.2: spanning probability for small depth-h prefixes
-- statement:
--   Fix $h\ge1$. There is $K>0$ depending only on $h$ with the following property. Let $r\ge2$, $m>r$, $0<p<1$, $\kappa\ge r$ and $\lambda\ge1$. Consider an AND or OR gate with $t\le m^\kappa$ input functions, every positive prefix of which is computed by a depth-at-most-$h$ circuit with at most $m^\kappa$ gates. Let $H_0$ have $v$ labeled vertices, $1\le v<m$, and let $H$ be its image under a uniform injection independent of $G\sim\mu_p$. There is an integer $D\ge v$ such that
--
--   $$D\le K\bigl(v+(\kappa\log_2m)^{h-1}\lambda\bigr),$$
--
--   $$\Pr[\exists j\in[t]:f_j\text{ spans }H]\le p^{-|E(H_0)|}\left[\left(\frac{eD}{m}\right)^v+m^{\kappa+rv+2}2^{-\lambda}\right].$$
--
--   This is the circuit-specific spanning estimate. The choice of $D$ must satisfy both conclusions for the same data.
--
--   **Formalization Note** The constant is chosen before $r,m,p,\kappa,\lambda$, the gate and its functions, $v$ and $H_0$. Each positive prefix has its own existential circuit. The Lean binder `L` denotes $\lambda$.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - encoding: $D=O_h(v+(\kappa\log m)^{h-1}\lambda)$ → one $K>0$ depending only on $h$ and an integer $D$ with the displayed explicit upper bound; reason: prevents choosing an instance-dependent large cutoff that would trivialize the probability bound
--   - encoding: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: pruning unused gates and deleting repeated sources preserve output and depth and cannot increase gate count
--   - encoding: monomials of the restricted real multilinear polynomial → nonzero Möbius coefficients on the exact subtype of missing edges; reason: the verified expansion identifies these coefficients with the source polynomial
--   - encoding: a uniform injection independent of $G$ → the reciprocal injection count times a sum over injections of the product-weight event probability; reason: the injection type is nonempty because $v<m$ and the finite product is the same independent distribution
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.13 (PDF p.15), Lemma 4.2, statement continues p.14 (PDF p.16)

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.2, pp.13–14 (PDF 15–16). The implicit constant depends on h alone. -/
theorem lemma_4_2 (h : ℕ) (hh : 1 ≤ h) :
    ∃ K : ℝ, 0 < K ∧ ∀ (r m : ℕ) (p κ L : ℝ),
      2 ≤ r → r < m → 0 < p → p < 1 → (r : ℝ) ≤ κ → 1 ≤ L →
      ∀ (isAnd : Bool) (inputs : List ((Edge m r → Bool) → Bool)),
      (inputs.length : ℝ) ≤ (m : ℝ) ^ κ →
      (∀ j : ℕ, 1 ≤ j → j ≤ inputs.length →
        ∃ C : MantriCVQ.ACCircuit (Edge m r), C.depth ≤ h ∧
          (C.gates.length : ℝ) ≤ (m : ℝ) ^ κ ∧
          ∀ x, C.eval x = abstractPrefix isAnd inputs j x) →
      ∀ (v : ℕ) (H₀ : Finset (Edge v r)), 1 ≤ v → v < m →
      ∃ D : ℕ, v ≤ D ∧
        (D : ℝ) ≤ K * ((v : ℝ) + (κ * Real.logb 2 (m : ℝ)) ^ (h - 1) * L) ∧
        prefixSpanningProbability p H₀ isAnd inputs ≤
          p ^ (-(H₀.card : ℝ)) *
            ((Real.exp 1 * (D : ℝ) / (m : ℝ)) ^ v +
              (m : ℝ) ^ (κ + (r : ℝ) * (v : ℝ) + 2) * (2 : ℝ) ^ (-L)) := by sorry

end HypercliqueAC0.FixedDepth
