-- Prove2me | Theorems.Thm_OAI_TorsionFreeZeroDivisors_TypedDiameter_diameter_tendsto
-- name    : OAI.TorsionFreeZeroDivisors.TypedDiameter.diameter_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T15:12:20.82162+00:00
-- url     : https://prove2.me/theorems/e515c8e1-51bc-4855-9537-0545d2858c64
-- title:
--   Lemma 2.3 (OpenAI) — component diameters of the girth-conditioned random graphs are $O(L)$ with probability tending to one
-- statement:
--   Fix the prescribed types of OpenAI's construction at level $n$, on side $A$ and on side $B$. Vertices are triples (line, slot, copy) in the projective plane over $\mathbb F_{128}$, with outgoing letters the points of the line together with the slot's extra letters. A matching is a fixed-point-free involution of the darts that sends each letter to its inverse letter. Let $\Omega_A(n)$ be the matchings of side $A$ whose graph has girth at least $L=L(\mathrm{size}(n))$, with $L(m)=\lfloor \ln m/100\rfloor$ and $\mathrm{size}(n)=2\cdot16513^2\,n$. Let $\mathrm{Bad}_A(n)\subseteq\Omega_A(n)$ be those whose vertex graph has two vertices in one connected component at distance greater than $D_0L$, for an explicit constant $D_0$. Define $\Omega_B$ and $\mathrm{Bad}_B$ in the same way. Then
--
--   $$\frac{|\mathrm{Bad}_A(n)|}{|\Omega_A(n)|}\xrightarrow[n\to\infty]{}0\qquad\text{and}\qquad\frac{|\mathrm{Bad}_B(n)|}{|\Omega_B(n)|}\xrightarrow[n\to\infty]{}0 .$$
--
--   Under the uniform distribution on girth-conditioned matchings, every component of each random graph therefore has diameter $O(\log n)$ with probability tending to one. Proposition 4.5 works on this event, and the short closures of Lemma 4.2 are built from it.
--
--   OpenAI, *A Torsion-Free Group Algebra with Zero Divisors* (September 23, 2026), p. 6: “Lemma 2.3. With conditional probability tending to one, every connected component of $\Gamma$ has diameter at most $D_0 L$, for a fixed constant $D_0$.”
--
--   **Formalization note.** The objects are OpenAI's (`TypedDiameter.ΩA`, `ΩB`, `diameterBadA`, `diameterBadB`, from the bundle `Def_TorsionFreeZeroDivisorsConstruction`). The level $n$ counts copies of the type table, so the paper's $n$ is $\mathrm{size}(n)$. Girth is measured in the subdivision graph, where each edge of $\Gamma$ has length $3$, so the condition reads $\ge 3L$ there. Its $D_0=803\,(\lceil1/\rho\rceil+1)$ comes from explicit constants $\rho$ and $C_0$. The inversion of letters pairs each extra letter with a point, and the remaining points in twos, through one fixed bijection chosen by `Fintype.equivOfCardEq` and not otherwise specified. The paper likewise pairs the letters “arbitrarily”. A ratio with empty denominator is $0$.
-- source:
--   OpenAI, A Torsion-Free Group Algebra with Zero Divisors, OpenAI Math Release, September 23, 2026, https://github.com/openai/math/blob/main/preprints/A-Torsion-Free-Group-Algebra-with-Zero-Divisors-September-23-2026/paper.pdf, p. 6, Lemma 2.3; Lean: https://github.com/openai/math, lean/OAI/Algebra/GroupRing (Apache-2.0), TypedDiameter.diameterA_tendsto and diameterB_tendsto

import Definitions.Def_TorsionFreeZeroDivisorsConstruction
import Mathlib

namespace OAI.TorsionFreeZeroDivisors.TypedDiameter

open scoped Classical
open Filter Topology

theorem diameter_tendsto :
    Tendsto (fun rep : ℕ => (diameterBadA rep).card/((ΩA rep).card:ℝ)) atTop (𝓝 0) ∧
      Tendsto (fun rep : ℕ => (diameterBadB rep).card/((ΩB rep).card:ℝ)) atTop (𝓝 0) := by
  sorry

end OAI.TorsionFreeZeroDivisors.TypedDiameter
