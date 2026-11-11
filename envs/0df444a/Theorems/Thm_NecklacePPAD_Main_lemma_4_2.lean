-- Prove2me | Theorems.Thm_NecklacePPAD_Main_lemma_4_2
-- name    : NecklacePPAD.Main.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:07:15.760133+00:00
-- url     : https://prove2.me/theorems/856b6a65-0cc5-49dc-945f-afbc2765bf08
-- title:
--   Lemma 4.2 (rigidity) — a split with ℓ(1) = 0 of a rigid necklace has exactly one cut inside each block and no other cut
-- statement:
--   Let $a$ be a necklace (every colour occurs an even number of times) that is rigid with blocks $(B(c))_{c}$, and let $\ell$ be a split with $\ell(1)=0$. Then every block contains exactly one cut inside it, and $\ell$ has no other cut. Consequently the first position of $B(c)$ has label $\tau(c)$, the number of blocks lying to the left of $B(c)$ modulo 2, and every position outside all blocks has label equal to the number of blocks to its left, modulo 2.
--
--   Differences from the source:
--   - encoding: 1-based positions [N], labels in {0,1}, ℓ(1) = 0 → 0-based positions, labels Bool (true = 1), lab ℓ 0 = false; reason: Lean indexing; the same labellings
--   - encoding: B(c) a set of consecutive positions → an interval [lo c, hi c] with lo c ≤ hi c < N; reason: B(c) holds more than b_c ≥ 0 beads of colour c, so it is nonempty, and a nonempty set of consecutive positions is such an interval
--   - encoding: a set C of n colours; balanced: exactly b_c of the 2b_c positions of colour c have label 1 → colours Fin n; 2·#{q : a_q = c, ℓ q} = count c; reason: same necklaces; the count of colour c is 2b_c
-- source:
--   Zeng, Wang, Cao, Dai, Wang, Necklace Splitting with Ten Beads per Colour is PPAD-Hard (STOC 2027 submission, sha256 d5b5449c…41ac), Lemma 4.2, p. 6 (PDF 8)

import Mathlib
import Definitions.Def_NecklacePPAD_Main_Rigid

set_option autoImplicit false

namespace NecklacePPAD.Main

open Blocks

/-- **Lemma 4.2 (rigidity)** (Zeng, Wang, Cao, Dai, Wang, *Necklace Splitting with Ten Beads per
Colour is PPAD-Hard*, STOC 2027 submission, sha256 d5b5449c…, p. 6 (PDF 8)). Let `a` be rigid with
blocks `(B(c))`, and let `ℓ` be a split with `ℓ(1) = 0`. Then every block contains exactly one cut
inside it and `ℓ` has no other cut; the first position of `B(c)` has label `τ(c)` (the number of
blocks to the left of `B(c)`, mod 2), and every position outside all blocks has label equal to the
number of blocks to its left, mod 2. Positions are 0-based (`ℓ(1)` is `lab ℓ 0`). -/
theorem lemma_4_2 (a : Necklace) (B : Blocks a.n) (ha : a.IsNecklace) (hB : a.IsRigid B)
    (ℓ : Fin a.N → Bool) (hℓ : a.IsSplit ℓ) (h0 : a.lab ℓ 0 = false) :
    (∀ c : Fin a.n, ∃! q, q ∈ a.cuts ℓ ∧ B.Inside c q) ∧
    (∀ q ∈ a.cuts ℓ, ∃ c : Fin a.n, B.Inside c q) ∧
    (∀ c : Fin a.n, (a.lab ℓ (B.lo c)).toNat = B.tau c) ∧
    (∀ q < a.N, (∀ c : Fin a.n, ¬ B.InBlock c q) → (a.lab ℓ q).toNat = B.blocksLeftOf q % 2) := by sorry

end NecklacePPAD.Main
