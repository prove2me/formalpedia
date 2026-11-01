-- Prove2me | Theorems.Thm_LPResolvingRM_lemma_1
-- name    : LPResolvingRM.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:41:59.394455+00:00
-- url     : https://prove2.me/theorems/ce3ddd8c-e9bf-4521-918e-3cafefbc70ba
-- title:
--   Lemma 1 — stability under nondegeneracy: a stability radius $L>0$ exists
-- statement:
--   Under Assumptions 1 and 2 there is a constant $L>0$, depending on $\mu$, $C$ and $b$, such that whenever
--   $$\max\Big\{\|\hat C-C\|_\infty,\ \|\hat\mu-\mu\|_\infty,\ \max_{i\in\mathcal I^*}|b_i-\hat b_i|,\ \max_{i\in\mathcal I'}(b_i-\hat b_i)\Big\}\le L,$$
--   the perturbed LP (8) $\max\hat\mu^\top y$ s.t. $\hat Cy+s=\hat b$, $y+z=\mathbf 1$, $y,s,z\ge0$ shares the optimal basis and the set of binding constraints of LP (6), with a unique optimal solution.
--
--   The regret bounds of the paper are stated in terms of such an $L$; this lemma is what makes them non-vacuous.
--
--   Differences from the source:
--   - encoding: P takes the finite support {(µ_j, c_j)} → p_j > 0 for every j and ∑_j p_j = 1; reason: a support point has positive probability; p is a probability vector
--   - reading: LP (8) shares the same optimal basis and set of binding constraints with LP (6) → LP (8) has a unique optimal solution with the same nonzero coordinates among (y, s, z) and the same binding set; reason: E.2 (p.50): 'the optimal solution to LP (8) is unique and it shares the same optimal basis and binding/non-binding structure'
--   - reading: ‖Ĉ − C‖_∞ for a matrix → the entrywise maximum max_{i,j} |Ĉ_{ij} − C_{ij}|; reason: reading R3: the proof of Proposition 2 (p.24) and E.2 (p.50) bound it entrywise
--   - encoding: standard form (6)/(8) with variables (y, s, z) → the y-part only, with s = b − Cy and z = 1 − y; reason: the feasible points correspond one to one with the same objective
--   - generalization: distinct support points (µ_j, c_j) → the pairs (µ_j, c_j) need not be distinct; the algorithm counts each index separately; reason: on distinct pairs this is the paper's model; the proofs never use distinctness
-- source:
--   Chen, Li, Ye, An Improved Analysis of LP-based Control for Revenue Management, arXiv:2101.11092v3, Lemma 1, p.9; Appendix E.2, pp.49–50

import Definitions.Def_LPResolvingRM_IsStabilityRadius

namespace LPResolvingRM

/-- **Lemma 1 (Stability under nondegeneracy)** (arXiv:2101.11092v3, p.9): "Under Assumption 1
and 2, there exists a positive constant L which depends on µ, C and b such that if
max{‖Ĉ − C‖∞, ‖µ̂ − µ‖∞, max_{i∈I∗}{|bᵢ − b̂ᵢ|}, max_{i∈I′}{bᵢ − b̂ᵢ}} ≤ L, then the following LP
shares the same optimal basis and set of binding constraints with LP (6)", the LP being (8).

**Formalization Note.** The conclusion is `LPResolvingRM.IsStabilityRadius`: (8) has a unique
optimal solution with the same nonzero coordinates and the same binding set (uniqueness from
E.2, p.50; `‖·‖_∞` of a matrix is the entrywise maximum, reading R3). -/
theorem lemma_1 {n m : ℕ} (I : Instance n m) (h1 : Assumption1 I) (h2 : Assumption2 I) :
    ∃ L : ℝ, 0 < L ∧ IsStabilityRadius I L := by sorry

end LPResolvingRM
