-- Prove2me | Theorems.Thm_IsingVectorBalancing_Subgaussian_lemma_6
-- name    : IsingVectorBalancing.Subgaussian.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T01:33:53.741609+00:00
-- url     : https://prove2.me/theorems/724d6c1b-2aa8-4b98-b886-574368568980
-- title:
--   Lemma 6 — Lorentz matrices of unit-ball families are Lorentzian
-- statement:
--   Let $C$ be any finite coordinate set and $u_c\in\mathbb R^d$ satisfy $\|u_c\|_2\le1$ for every $c\in C$. The Lorentz matrix
--   $$A(c,c')=1-\langle u_c,u_{c'}\rangle$$
--   is symmetric, entrywise nonnegative, and has at most one positive eigenvalue counted with multiplicity. No restriction on repeated or parallel vectors is imposed. This supplies a spectral certificate for the matrices in the polynomial inequality.
--
--   Differences from the source:
--   - encoding: real symmetric matrix with at most one positive eigenvalue → real Hermitian matrix whose positive eigenvalue indices have cardinality at most one; reason: real Hermitian symmetry is symmetry and the full eigenvalue list counts multiplicity
--   - generalization: the source does not discuss zero dimensional input vectors → d = 0 is included; reason: the Lorentz matrix is then the all-ones matrix, which satisfies the same spectral statement; all source dimensions remain included
-- source:
--   Heng Guo, Daniel Spielman, Xinyuan Zhang, STOC 2027 submission #1240 (October 2026), Subgaussian Vector Balancing by an Ising Model, p. 5 (PDF 6), Lemma 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1240.pdf

import Definitions.Def_IsingVectorBalancing_Subgaussian_Lorentz

set_option autoImplicit false

namespace IsingVectorBalancing.Subgaussian

theorem lemma_6 {C : Type*} [Fintype C] [DecidableEq C] {d : ℕ}
    (u : C → Vec d) (hu : ∀ c, ‖u c‖ ≤ 1) :
    IsLorentzian (lorentzMatrix u) := by sorry

end IsingVectorBalancing.Subgaussian
