-- Prove2me | Theorems.Thm_InvariantMoneySecurity_Decomposition_orbit_fixed_points
-- name    : InvariantMoneySecurity.Decomposition.orbit_fixed_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:57:19.042205+00:00
-- url     : https://prove2.me/theorems/ae284d05-1cc4-4f8a-b55c-e8d85d7bb2ca
-- title:
--   Lemma 3.1 — orbit states as fixed points of the walk
-- statement:
--   Let $X$ be a finite nonempty ground set of $n$-bit objects, let $S$ be a nonempty inverse-closed set of moves, and let $C(x)$ be the orbit of an object $x$. For the lazy walk $\widehat B$, the normalized uniform orbit vector $\psi_{C(x)}$ satisfies
--   $$\widehat B\psi_{C(x)}=\psi_{C(x)},\qquad\{v:\operatorname{supp}(v)\subseteq C(x),\ \widehat Bv=v\}=\mathbb C\psi_{C(x)}.$$
--   Thus the eigenvalue one on every orbit block is simple, with the source's uniform orbit vector as eigenvector. This includes singleton orbits and requires no rapid-mixing assumption. It identifies the accepted subspace used in the quantitative verifier comparison.
--
--   Differences from the source:
--   - generalization: finite data of an efficient invariant money family at n ≥ 1 → any finite nonempty inverse-closed distinct move system, including n = 0; reason: the spectral conclusions use only the finite permutation system; every source instance specializes to these data
--   - encoding: logical object registers and public serials → padded qubit registers, polynomial-width public serial encoding, and a dummy n = 0 instance; reason: valid states embed isometrically; invalid encodings reject; reversible serial padding preserves equality and mint weights; finite initial values do not affect negligibility
-- source:
--   Hans Schmiedel, Jiangshan Yu, STOC 2027 submission #164 (October 2026), p. 10, Lemma 3.1, equation (6)

import Definitions.Def_InvariantMoneySecurity_Decomposition_FiniteScheme
set_option autoImplicit false

namespace InvariantMoneySecurity.Decomposition

/-- Lemma 3.1, p. 10, equation (6); stated for all finite inverse-closed move systems.
The embedded orbit eigenspace consists exactly of scalar multiples of the uniform vector. -/
theorem orbit_fixed_points {n : ℕ} (D : FiniteScheme n) (x : D.Object) :
    D.walk.mulVec (D.orbitVector x) = D.orbitVector x ∧
    ∀ v : Bits n → ℂ,
      (∀ y, y ∉ D.orbit x → v y = 0) → D.walk.mulVec v = v →
      ∃ c : ℂ, v = c • D.orbitVector x := by sorry

end InvariantMoneySecurity.Decomposition
