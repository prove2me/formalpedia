-- Prove2me | Theorems.Thm_FourBlockIP350_Main_uniform_idp
-- name    : FourBlockIP350.Main.uniform_idp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:36:58.858918+00:00
-- url     : https://prove2.me/theorems/9e2dd664-3c13-48ae-892f-cb7cad45648c
-- title:
--   Proposition 2.6 — Uniform n-fold IDP dilation
-- statement:
--   There is one total computable positive integer dilation $N(k,\bar\Delta)$, independent of the number of bricks and right-hand side, and absolute constants $C,c>0$, such that
--   $$N(k,\bar\Delta)\le 2^{C(k\bar\Delta)^{ck^2}}.$$
--   For every $k,\bar\Delta\ge1$, every positive number of bricks and every nonuniform generalized n-fold matrix $Q$ with blocks at most $k\times k$ and entries bounded by $\bar\Delta$, the polyhedron $\{z\ge0:Qz=N(k,\bar\Delta)w\}$ has the IDP for every integral $w$.
--
--   This is the structural uniformity needed for one period to work across all local subproblems.
--
--   Differences from the source:
--   - encoding: N=2^{(k Δbar)^{O(k²)}} → N≤2^{C(k Δbar)^{c k²}} with uniform positive natural C,c and a machine-computable N; reason: an explicit uniform upper-bound interpretation of the asymptotic order, allowing a constant multiplier to cover small parameter values; no numerical hidden constants are chosen
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 5, Proposition 2.6

import Mathlib
import Definitions.Def_FourBlockIP350_Main_BinaryEncoding
import Definitions.Def_FourBlockIP350_Main_Decomposition

namespace FourBlockIP350.Main

open scoped BigOperators

theorem uniform_idp :
    ∃ N : ℕ → ℕ → ℕ, ComputablePairFunction N ∧
    ∃ C c : ℕ, 0 < C ∧ 0 < c ∧
    ∀ k Δ : ℕ, 0 < k → 0 < Δ →
      0 < N k Δ ∧ N k Δ ≤ 2 ^ (C * (k * Δ) ^ (c * k^2)) ∧
      UniformDilation k Δ (N k Δ) := by sorry

end FourBlockIP350.Main
