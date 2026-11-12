-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch02_normalizer_map_of_coprime_kernel
-- name    : OddOrder.Isaacs.Ch02.normalizer_map_of_coprime_kernel
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:54:05.644043+00:00
-- url     : https://prove2.me/theorems/7bac0bf6-915b-4d4c-bf8b-0c317d54fea2
-- title:
--   Isaacs Lemma 2.17: the normalizer of a $p$-subgroup in a $p'$-quotient is the image of its normalizer
-- statement:
--   Let $G$ be a finite group, $N\trianglelefteq G$ a normal subgroup, $p$ a prime with $p\nmid|N|$, and $P\le G$ a $p$-subgroup. Let $f:G\to G/N$ be the quotient map. Then
--   $$N_{G/N}\bigl(f(P)\bigr)=f\bigl(N_G(P)\bigr).$$
--
--   The proof is a Frattini argument using Sylow's theorem.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch02_Subnormality/Main.lean#L481-L773

import Definitions.Def_OddOrder_Isaacs_Ch02_Subnormality_Theorem211Wielandt

open OddOrder.Isaacs.Ch01

namespace OddOrder.Isaacs.Ch02

section

variable {G : Type*} [Group G]

set_option maxHeartbeats 1200000 in
-- 長い構成的証明 (Sylow II + Frattini, ↥M 内で構築 + G への持ち上げ) のため heartbeat を増やす.

theorem normalizer_map_of_coprime_kernel [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    [Fact p.Prime] (hp_coprime : ¬ p ∣ Nat.card N)
    {P : Subgroup G} (hP_pgroup : IsPGroup p P) :
    Subgroup.normalizer ((P.map (QuotientGroup.mk' N)) : Subgroup (G ⧸ N))
      = (Subgroup.normalizer P).map (QuotientGroup.mk' N) := by sorry

end

end OddOrder.Isaacs.Ch02
