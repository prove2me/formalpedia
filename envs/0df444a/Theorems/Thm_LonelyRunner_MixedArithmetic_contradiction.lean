-- Prove2me | Theorems.Thm_LonelyRunner_MixedArithmetic_contradiction
-- name    : LonelyRunner.MixedArithmetic.contradiction
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:38.06056+00:00
-- url     : https://prove2.me/theorems/9aa5f698-c725-432f-ac35-7d7fb5bc9ef9
-- title:
--   Least-unit uniqueness is incompatible with the mixed-window constraints
-- statement:
--   Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. Let $n,r,s,m,k,B,D\in\mathbb N$ satisfy $r<s<n$, $m,D\ge2$, $mD<k+m$, $\operatorname{GW}(n,s,k)$, $B<r$, $DB=k(s-r)$, and $k(n-s)\le B$. Suppose $B$ is the least natural number at least $n-r$ coprime to $r$. Then the following assertion is impossible:
--
--   $$\forall w\in\mathbb N,\quad n-r\le w<2(n-r),\ \gcd(r,w)=1,\ w<n-k(n-s)\Longrightarrow w=B.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MixedArithmetic.lean, lines 8–67, declaration LonelyRunner.MixedArithmetic.contradiction. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.MixedArithmetic
open SeparatedReplacements GWArithmetic GWGrowth FlankReduction SecondUnit

set_option maxHeartbeats 1800000 in

theorem LonelyRunner.MixedArithmetic.contradiction {n r s m k B D : ℕ}
    (hrs : r < s) (hsn : s < n) (hm : 2 ≤ m) (hD2 : 2 ≤ D)
    (hnear : m*D < k+m) (hgw : GW n s k) (hBr : B < r)
    (hDB : D*B=k*(s-r)) (hBkc : k*(n-s) ≤ B)
    (hBlo : n-r ≤ B) (hBcop : Nat.Coprime r B)
    (hmin : ∀ b, n-r ≤ b → Nat.Coprime r b → B ≤ b)
    (hforced : ∀ w, n-r ≤ w → w < 2*(n-r) → Nat.Coprime r w →
      w < n-k*(n-s) → w=B) : False := by sorry
