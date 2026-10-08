-- Prove2me | Theorems.Thm_GOSNIZK_BGNCommit_witness_indistinguishability
-- name    : GOSNIZK.BGNCommit.witness_indistinguishability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T11:25:30.037992+00:00
-- url     : https://prove2.me/theorems/62b2653e-4d2a-410f-84db-b92c619edfeb
-- title:
--   Proof of Theorem 2 — on a hiding key the proof $\pi$ is unique, so both witnesses give the same proof
-- statement:
--   Let $(p, q, \mathbb G, \mathbb G_T, e, g)$ be a BGN bilinear group with $n = pq$ and let $h = g^x$, $x \in \mathbb Z_n^*$, be a perfectly hiding key. Then
--
--   1. for every $c \in \mathbb G$ there is exactly one $\pi \in \mathbb G$ with $e(c, cg^{-1}) = e(h, \pi)$;
--   2. if $c = g^0 h^{r_0} = g^1 h^{r_1}$, then the two witnesses produce the same proof:
--   $$P_{01}(ck, 0, r_0) = P_{01}(ck, 1, r_1).$$
--
--   Since the prover is deterministic, the second item is the perfect witness indistinguishability of the 0/1 proof: the proof reveals nothing about which opening was used.
-- source:
--   Groth, Ostrovsky, Sahai, New Techniques for Noninteractive Zero-Knowledge, J. ACM 59(3) (2012), authors' version of March 7, 2011, p. 9, proof of Theorem 2 (witness indistinguishability)

import Mathlib
import Definitions.Def_GOSNIZK_BGNCommit_BGNSetup
import Definitions.Def_GOSNIZK_BGNCommit_Scheme

namespace GOSNIZK.BGNCommit

theorem witness_indistinguishability {G GT : Type*} [CommGroup G] [Fintype G]
    [CommGroup GT] [Fintype GT] (S : BGNSetup G GT) (h : G) (x : ZMod S.n) (hkey : S.IsHidingKey h x) :
    (∀ c : G, ∃! π : G, S.e c (c * S.g⁻¹) = S.e h π) ∧
      ∀ r₀ r₁ : ZMod S.n, S.com h 0 r₀ = S.com h 1 r₁ → S.P01 h 0 r₀ = S.P01 h 1 r₁ := by sorry

end GOSNIZK.BGNCommit
