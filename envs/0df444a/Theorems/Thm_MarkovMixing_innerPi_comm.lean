-- Prove2me | Theorems.Thm_MarkovMixing_innerPi_comm
-- name    : MarkovMixing.innerPi_comm
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T01:08:07.672244+00:00
-- url     : https://prove2.me/theorems/4079bd9e-274e-4cdd-8546-9ca3b2cff283
-- title:
--   The $ℓ^2(π)$ inner product is symmetric
-- statement:
--   For a weight $\pi : V \to \mathbb{R}$ on a finite set $V$ and functions
--   $f, g : V \to \mathbb{R}$, the $\ell^2(\pi)$ pairing
--   $\langle f, g \rangle_\pi = \sum_{x \in V} \pi(x)\, f(x)\, g(x)$ is symmetric:
--
--   $$
--   \langle f, g \rangle_{\pi} \;=\; \langle g, f \rangle_{\pi}.
--   $$
--
--   Trivial to prove and constantly needed: the spectral theory of a reversible chain is carried out
--   in $\ell^2(\pi)$, where almost every manipulation reorders the two arguments of the pairing.
--   Stating it once avoids an `unfold`-and-`ring` step in each later proof.
-- source:
--   D. A. Levin, Y. Peres and E. L. Wilmer, Markov Chains and Mixing Times, 2nd ed., AMS 2017, §12.1; carved from the accepted proof of DiaconisStroock.Poincare.proposition_1, https://prove2.me/submissions/b36a2a77-0ed1-410e-b982-dafb4dc643a6

import Mathlib
import Definitions.Def_mm_spectral

open scoped BigOperators
open scoped Matrix
open MarkovMixing
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem MarkovMixing.innerPi_comm (π g h : V → ℝ) : innerPi π g h = innerPi π h g := by sorry
