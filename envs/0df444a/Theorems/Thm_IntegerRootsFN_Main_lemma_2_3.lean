-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_2_3
-- name    : IntegerRootsFN.Main.lemma_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:52:07.844897+00:00
-- url     : https://prove2.me/theorems/e9ec6359-f152-4584-88ac-3fa93c224776
-- title:
--   Lemma 2.3 — perturbation proximity and logarithmic root size
-- statement:
--   Let $g\in\mathbb Z[x]$ have degree $d\ge1$ and coefficients of magnitude less than $2^b$, where $b\ge1$. Let $\widehat g\in\mathbb C[x]$ have the same degree, with all roots $\beta_1,\ldots,\beta_d$ counted with multiplicity. If
--
--   $$\delta=\|\widehat g-g\|_1<\frac1{8\cdot9^d(2^b\sqrt{d+1}+1)},$$
--
--   then every root of $g$ has distance strictly less than $1/8$ to at least one $\beta_i$, and
--
--   $$\sum_{i=1}^d\log_2\max(1,|\beta_i|)\le b+\tfrac12\log_2(d+1)+2.$$
--
--   The root family is pinned by the complete factorization product and has $d$ entries even when roots repeat. No dyadic, monic, simple-root or real-rooted restriction is imposed. These conclusions control both approximation coverage and aggregate root magnitude.
--
--   Differences from the source:
--   - reading: within distance 1/8 → distance strictly less than 1/8; reason: the contradiction proof on p.6 assumes all distances at least 1/8, and Proposition 3.4 uses the resulting strict inequality
--   - encoding: d roots counted with multiplicity → a Fin d family whose full linear-factor product equals the polynomial divided by its nonzero leading scalar; reason: the factorization equality retains every repeated root; no injective matching of roots to approximants is asserted
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 6, Lemma 2.3

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

namespace IntegerRootsFN.Main

/-- “Within” is strict, as the source's proof on p.6 establishes. -/
theorem lemma_2_3 (d b : ℕ) (g : Polynomial ℤ) (hg : Valid g d b)
    (ĝ : Polynomial ℂ) (hdegree : ĝ.natDegree = d) (β : Fin d → ℂ)
    (hβ : ListsRoots ĝ β)
    (hδ : normOne (ĝ - complexify g) < perturbationThreshold d b) :
    CoversRoots (complexify g) β ∧ logRootSize β ≤ rootSizeBound d b := by sorry

end IntegerRootsFN.Main
