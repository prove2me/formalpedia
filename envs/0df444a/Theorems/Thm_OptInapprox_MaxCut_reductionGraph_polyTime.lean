-- Prove2me | Theorems.Thm_OptInapprox_MaxCut_reductionGraph_polyTime
-- name    : OptInapprox.MaxCut.reductionGraph_polyTime
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T14:40:37.942234+00:00
-- url     : https://prove2.me/theorems/332be049-e1ad-4435-a74c-4f81e5f9bc1d
-- title:
--   Proof of Theorem 1, §8 — for a fixed label-set size, the Unique Label Cover → MAX-CUT reduction of §8.1 is polynomial-time computable
-- statement:
--   Fix natural numbers $M_0$ (the label-set size), $R$, $K$, $p$ and $q$. Then the map sending a Unique Label Cover instance $\mathcal L$ with label set $[M_0]$ to the weighted MAX-CUT instance $G_{R,K,p,q}(\mathcal L)$ of the §8.1 reduction (`reductionGraph`) is computable in polynomial time on encodings: there is a function $g$ from strings over the Label Cover alphabet to strings over the MAX-CUT alphabet, computable in polynomial time by a one-tape Turing machine, such that
--   $$g\big(\mathrm{enc}_{\mathrm{ULC}}(\mathcal L)\big)=\mathrm{enc}_{\mathrm{MaxCut}}\big(G_{R,K,p,q}(\mathcal L)\big)\qquad\text{for every }\mathcal L\text{ with }M=M_0.$$
--
--   This is the "the reduction runs in polynomial time" part of the proof of Theorem 1: since the label-set size $M_0$ is a constant, the Long Code tables have constant size $2^{M_0}$, and the instance has $|W|\,R\,2^{M_0}$ vertices and at most $|V|\cdot 2K|W|^2\cdot R^2\,4^{M_0}(2q)^{M_0}$ edges (with multiplicity), each written with $O(|W|R2^{M_0})$ symbols, so the output has polynomial length and is produced by nested loops over $v$, pairs of neighbours of $v$, copies, and the constant-size cube.
--
--   **Formalization Note.** Encodings are the ones of the mission's definitions (`encULC`: $|V|,|W|,M$ in unary and, for every pair $(v,w)$ in lexicographic order, a non-edge marker or an edge marker followed by the table of $\sigma_{v,w}$; `encMaxCut`: the vertex count and the endpoints of every listed edge in unary). The output depends only on data present in $\mathrm{enc}_{\mathrm{ULC}}(\mathcal L)$ (the permutations are consulted only on edges), so $g$ is well defined. Polynomial-time computability is Cook's `PolyTimeComputable`.
-- source:
--   Khot, Kindler, Mossel & O'Donnell, Optimal Inapproximability Results for MAX-CUT and Other 2-Variable CSPs?, SIAM J. Comput. 37(1), 2007 (authors' version of February 7, 2007), §8 (the reduction of §8.1 used in the proof of Theorem 1, p. 11), polynomial running time for constant M

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_ReductionGraph

namespace OptInapprox.MaxCut

theorem reductionGraph_polyTime (M₀ R K p q : ℕ) :
    ∃ g : List ULCSym → List MCSym, CookPvsNP.PolyTimeComputable g ∧
      ∀ L : ULC, L.M = M₀ → g (encULC L) = encMaxCut (reductionGraph L R K p q) := by
  sorry

end OptInapprox.MaxCut
