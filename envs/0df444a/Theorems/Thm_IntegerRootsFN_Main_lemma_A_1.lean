-- Prove2me | Theorems.Thm_IntegerRootsFN_Main_lemma_A_1
-- name    : IntegerRootsFN.Main.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:51:57.914468+00:00
-- url     : https://prove2.me/theorems/0ad34aa4-e19e-4494-b45c-7a06c5737d6b
-- title:
--   Lemma A.1 — both Pellet alternatives
-- statement:
--   Let $q(x)=\sum_{k=0}^dq_kx^k\in\mathbb C[x]$ have degree $d\ge1$. Both alternatives hold:
--
--   1. If $|q_0|>\sum_{k=1}^d|q_k|$, then $q$ has no root in the closed unit disk.
--   2. If $|q_0|\le\sum_{k=1}^d|q_k|$, then
--
--   $$\exists z\in\mathbb C:\quad q(z)=0,\quad |z|\le\tfrac32d.$$
--
--   The second alternative includes equality and $q_0=0$. This is a statement about arbitrary complex polynomials, with no integrality, separation or simple-root hypothesis, and supplies both branches of the exclusion test.
--
--   Differences from the source: none.
-- source:
--   Yansong Feng, Itamar Nir, STOC 2027 submission #1353 (October 2026), p. 12, Lemma A.1

import Mathlib
import Definitions.Def_IntegerRootsFN_Main_PolynomialData

set_option autoImplicit false

namespace IntegerRootsFN.Main

theorem lemma_A_1 (d : ℕ) (hd : 1 ≤ d) (q : Polynomial ℂ) (hq : q.natDegree = d) :
    ((∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) < ‖q.coeff 0‖ →
      ∀ z : ℂ, ‖z‖ ≤ 1 → ¬q.IsRoot z) ∧
    (‖q.coeff 0‖ ≤ (∑ k ∈ Finset.range d, ‖q.coeff (k + 1)‖) →
      ∃ z : ℂ, q.IsRoot z ∧ ‖z‖ ≤ (3 : ℝ) / 2 * d) := by sorry

end IntegerRootsFN.Main
