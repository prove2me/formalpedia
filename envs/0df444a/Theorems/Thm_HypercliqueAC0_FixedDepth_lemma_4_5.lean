-- Prove2me | Theorems.Thm_HypercliqueAC0_FixedDepth_lemma_4_5
-- name    : HypercliqueAC0.FixedDepth.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T19:12:22.060125+00:00
-- url     : https://prove2.me/theorems/f479d221-07e1-4b93-b3c0-6c92b18dc487
-- title:
--   Lemma 4.5: the union bound over gates and planted positions
-- statement:
--   Fix integers $h\ge1$ and $r\ge2$. There is a threshold $m_0$, depending only on $h,r$, such that the following holds whenever $m\ge m_0$. Let $s\ge r$, $1\le\ell<m$, $0<p<1$, $\kappa\ge\max\{r+1,\ell/2\}$ and $0<\Lambda\le1$, with
--
--   $$\kappa^h(\log_2m)^{h+1}\le\Lambda m,\qquad \binom{s-1}{r-1}\ln(1/p)\le\ln(1/\Lambda).$$
--
--   Let $C$ have depth at most $h+1$ and $G(C)\le m^\kappa/2$ gates. Draw a uniform injection $\phi:[\ell]\hookrightarrow[m]$ independently of $G\sim\mu_p$ and put $A=\phi([\ell])$. If $\mathcal E$ is the event that some gate of depth at most $h$ has a monomial touching more than $s$ vertices after restriction by $\rho_{K_A}$, then
--
--   $$\Pr[\mathcal E]\le G(C)4^\ell\Lambda^sp^{-\binom sr}+m^{-\kappa}.$$
--
--   This is the paper's bound in its maximal-event form, which implies the same bound for every event described there.
--
--   **Formalization Note** The threshold is selected before $s,\ell,p,\kappa,\Lambda,C$. Gate depth is computed separately for each gate.
--
--   Differences from the source:
--   - encoding: $[m]=\{1,\ldots,m\}$ and $r$-subsets → $\mathrm{Fin}\,m$ with edge subtype of cardinality $r$; reason: a relabeling bijection preserves the entire hypergraph and all circuit instances
--   - encoding: Boolean-cube Fourier coefficients and product-measure probabilities → Boolean functions converted to real indicators and finite weighted sums over all assignments; reason: the finite product distribution and every coefficient have the same values
--   - encoding: sufficiently large $m$ in terms of $h,r$ → an existential natural threshold chosen after $h,r$ and before all remaining data; reason: this is the uniform quantifier order specified by the proof on p.17
--   - encoding: an event on which some gate of depth at most $h$ has the stated monomial → the maximal event that such a gate exists; reason: the maximal event is itself allowed by the source, and every contained event has no larger probability
--   - generalization: the §3.2 convention that every gate reaches the output → arbitrary circuits, including unused gates and repeated input sources, with gate count equal to the gate-list length; reason: the proof on p.17 bounds each gate of depth at most h through its ancestor subcircuit, regardless of whether it reaches the designated output; source circuits are included, and repeated sources add no new prefix events
--   - encoding: monomials of the restricted real multilinear polynomial → nonzero Möbius coefficients on the exact subtype of missing edges; reason: the verified expansion identifies these coefficients with the source polynomial
--   - encoding: a uniform injection independent of $G$ → the reciprocal injection count times a sum over injections of the product-weight event probability; reason: the injection type is nonempty because $1\le\ell<m$ and the finite product is the same independent distribution
-- source:
--   Nikolai Chukhin, Exhaustive Search Is Hard to Beat in Constant Depth for Hyperclique and Orthogonal Vectors, STOC 2027 submission #830 (October 2026), source.pdf SHA-256 bd73fd887fe562527226e0ea2da24a55552a73cf89c2e90406a28965424a12de, p.17 (PDF p.19), Lemma 4.5

import Mathlib
import Definitions.Def_HypercliqueAC0_FixedDepth_Planting

noncomputable section

namespace HypercliqueAC0.FixedDepth
attribute [local instance] Classical.propDecidable Classical.decEq
open scoped BigOperators

/-- Lemma 4.5, p.17 (PDF 19). The threshold depends only on h and r.
The event is the maximal event described in the paper. -/
theorem lemma_4_5 (h r : ℕ) (hh : 1 ≤ h) (hr : 2 ≤ r) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ (s ℓ : ℕ) (p κ Λ : ℝ),
      r ≤ s → 1 ≤ ℓ → ℓ < m → 0 < p → p < 1 →
      max ((r : ℝ) + 1) ((ℓ : ℝ) / 2) ≤ κ → 0 < Λ → Λ ≤ 1 →
      κ ^ h * (Real.logb 2 (m : ℝ)) ^ (h + 1) ≤ Λ * (m : ℝ) →
      (Nat.choose (s - 1) (r - 1) : ℝ) * Real.log (1 / p) ≤ Real.log (1 / Λ) →
      ∀ C : MantriCVQ.ACCircuit (Edge m r), C.depth ≤ h + 1 →
        (C.gates.length : ℝ) ≤ (m : ℝ) ^ κ / 2 →
        largeGateProbability p ℓ h s C ≤
          (C.gates.length : ℝ) * (4 : ℝ) ^ ℓ * Λ ^ s *
            p ^ (-(Nat.choose s r : ℝ)) + (m : ℝ) ^ (-κ) := by sorry

end HypercliqueAC0.FixedDepth
