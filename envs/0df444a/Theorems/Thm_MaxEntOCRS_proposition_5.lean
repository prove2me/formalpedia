-- Prove2me | Theorems.Thm_MaxEntOCRS_proposition_5
-- name    : MaxEntOCRS.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:35:44.382881+00:00
-- url     : https://prove2.me/theorems/c5014228-a1d2-44ad-881d-378ee116266d
-- title:
--   Proposition 5 (Heilmann–Lieb) — $P_H(z) \ne 0$ on the right half-plane, so the free-set law $\nu$ is right-half-plane zero-free
-- statement:
--   1. (Proposition 5, Heilmann–Lieb.) For every finite loopless multigraph $H$ with activities $t \ge 0$, the monomer polynomial satisfies
--   $$
--   P_H(z) \ne 0 \qquad \text{whenever } \operatorname{Re} z_j > 0 \text{ for every } j .
--   $$
--   2. For every finite loopless multigraph $G$ with activities $t \ge 0$ and distinct vertices $u, v$, the law $\nu$ of the free neighbourhood $F$ (Section 3) is a probability distribution on the subsets of $[k]$ and is right-half-plane zero-free: its generating polynomial $g_\nu(z) = \sum_F \nu(F) \prod_{i\in F} z_i$ has no zeros when all real parts are positive.
--
--   This is the only property of monomer–dimer measures that Lemmas 6 and 8 use.
--
--   Differences from the source:
--   - encoding: ν is the law of F (a probability distribution by construction) → ν is defined by a formula, and its nonnegativity and total mass 1 are stated as conclusions; reason: makes the law property explicit; no instance changes
--   - encoding: G′ = G − u − v and its monomer–dimer measure → matchings of G covering neither u nor v, with the restricted measure; reason: the same measure as on the induced subgraph; no subgraph type
--   - encoding: neighbours y₁, …, y_k indexed by [k] → the finite subtype of the neighbour set N; reason: an enumeration is not needed; same index set up to relabelling
-- source:
--   Chen–Wang, Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality, STOC 2027 submission (manuscript sha256 06944af9…), Proposition 5, p.6 (proof in A.3, p.12), and the paragraph after it, p.6

import Mathlib
import Definitions.Def_EdmondsMatching65_Polyhedron_Graph
import Definitions.Def_MaxEntOCRS_monomerPoly
import Definitions.Def_MaxEntOCRS_nbrSet
import Definitions.Def_MaxEntOCRS_freeLaw
import Definitions.Def_MaxEntOCRS_IsRHPZeroFree

namespace MaxEntOCRS

/-- Proposition 5 (Heilmann–Lieb [HL72]; Chen–Wang, *Optimal Maximum-Entropy Stationary Contention Resolution for General Matchings via a Sharp Two-Point Monomer–Dimer Inequality*, STOC 2027 submission manuscript (sha256 06944af9…2d0462c), p.6; A.3, p.12) and its consequence for the
free-set law (§4, p.6). (i) For every finite loopless multigraph `H` with nonnegative
activities, the monomer polynomial `P_H(z)` does not vanish when `Re z_j > 0` for every `j`.
(ii) For distinct vertices `u, v` of `G` with nonnegative activities, the law `ν` of the free
neighbourhood is a probability distribution that is right-half-plane zero-free. -/
theorem proposition_5 :
    (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (H : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ), (∀ e, 0 ≤ t e) →
        ∀ z : V → ℂ, (∀ j, 0 < (z j).re) → monomerPoly H t z ≠ 0) ∧
      (∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E] (G : EdmondsMatching65.Polyhedron.Graph V E) (t : E → ℝ), (∀ e, 0 ≤ t e) →
        ∀ u v : V, u ≠ v →
          (∀ F, 0 ≤ freeLaw G t u v F) ∧ ∑ F, freeLaw G t u v F = 1 ∧
            IsRHPZeroFree (freeLaw G t u v)) := by sorry

end MaxEntOCRS
