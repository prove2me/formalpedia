-- Prove2me | Theorems.Thm_HILL_PRG_affine_prefix_collision_count
-- name    : HILL.PRG.affine_prefix_collision_count
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-18T01:40:25.927788+00:00
-- url     : https://prove2.me/theorems/ecf95c36-f503-45a8-ba67-963507175e70
-- title:
--   Exact collision count for a binary affine hash prefix
-- statement:
--   Fix integers $0\le j\le N$ and distinct binary strings $x,y$ of length $N$. A key consists of $N$ rows of $N+1$ bits each. The first bit of each row is an offset and the remaining $N$ bits are coefficients. The hash of an input is the list of the first $j$ row evaluations, where each row adds its offset to the binary inner product of its coefficients and the input.
--
--   The number of keys for which $x$ and $y$ have the same hash, multiplied by $2^j$, equals the total number $2^{N(N+1)}$ of keys. Under a uniform key the collision probability is therefore $2^{-j}$. The unused rows remain part of the key, so its length is fixed as the prefix width varies. This gives a concrete collision-universal family for the extraction step in HILL Construction 4.15.
-- source:
--   Supporting counting lemma for the use of universal hashing in Håstad, Impagliazzo, Levin, and Luby, A Pseudorandom Generator from Any One-Way Function, SIAM J. Comput. 28(4), 1999, Definition 4.6, Lemma 4.8 and Construction 4.15. https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf

import Definitions.Def_HILL_PRG_Model
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.FinRange

open HILL.PRG
open scoped BigOperators

namespace HILL.PRG

theorem affine_prefix_collision_count (N j : ℕ) (hj : j ≤ N) (x y : Bits)
    (hx : x ∈ cube N) (hy : y ∈ cube N) (hxy : x ≠ y) :
    let affine := fun (r w : Bits) =>
      (List.range j).map fun i =>
        Bool.xor (r.getD (i * (N + 1)) false)
          (ip ((r.drop (i * (N + 1) + 1)).take N) (w.take N))
    ((cube (N * (N + 1))).filter (fun r => affine r x = affine r y)).card *
      2 ^ j = 2 ^ (N * (N + 1)) := by sorry

end HILL.PRG
