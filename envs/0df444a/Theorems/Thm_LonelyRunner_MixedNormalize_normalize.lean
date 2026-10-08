-- Prove2me | Theorems.Thm_LonelyRunner_MixedNormalize_normalize
-- name    : LonelyRunner.MixedNormalize.normalize
-- status  : Proved
-- author  : @Whunt003
-- created : 2026-10-07T18:54:27.833373+00:00
-- url     : https://prove2.me/theorems/33d01495-228f-4bdc-acbd-9ce64a41b8c3
-- title:
--   Normalize a least failed unit into arithmetic shape parameters
-- statement:
--   Write $\operatorname{GW}(n,r,m)$ for the assertion that no natural number $b$ with $n-r\le b<m(n-r)$ is coprime to $r$. Let $n,r,s,m,k,B,D\in\mathbb N$ satisfy $r<s<n$, $m\ge2$, $D\ge2$, $mD<k+m$, $\operatorname{GW}(n,s,k)$, $DB=k(s-r)$, and $k(n-s)\le B$. Assume $B$ is the least natural number at least $n-r$ coprime to $r$. Then there are positive natural numbers $e,d,u$ such that
--
--   $$D=ed,\quad k=e(d+1),\quad B=(d+1)u,\quad s=r+du,\quad\gcd(u,s)=1,\quad k(n-s)\le u.$$
--
--   AI-assisted research and formalization. Independent mathematical review and novelty assessment remain outstanding.
-- source:
--   Wade Hunter, AI-assisted lonely-runner research, https://github.com/huntrontrakkr/lonely-runner; local source snapshot e63781c7cf2101e453103bfd9b215b72d162d05d, lean/LonelyRunner/MixedNormalize.lean, lines 9–71, declaration LonelyRunner.MixedNormalize.normalize. The snapshot identifies the submitted local source, not a publicly hosted commit.

import Mathlib
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Primorial
import Definitions.Def_LRC_ComponentRigidity_Defs

open LonelyRunner
open LonelyRunner.MixedNormalize
open SeparatedReplacements SecondUnit GWArithmetic

set_option maxHeartbeats 1500000 in

theorem LonelyRunner.MixedNormalize.normalize {n r s m k B D : ℕ}
    (hrs : r < s) (hsn : s < n) (hm : 2 ≤ m) (hD2 : 2 ≤ D)
    (hnear : m*D < k+m) (hgw : GW n s k)
    (hDB : D*B=k*(s-r)) (hBkc : k*(n-s) ≤ B)
    (hBlo : n-r ≤ B) (hBcop : Nat.Coprime r B)
    (hmin : ∀ b, n-r ≤ b → Nat.Coprime r b → B ≤ b) :
    ∃ e d u : ℕ, 0 < e ∧ 0 < d ∧ 0 < u ∧ D=e*d ∧ k=e*(d+1) ∧
      B=(d+1)*u ∧ s=r+d*u ∧ Nat.Coprime u s ∧ k*(n-s) ≤ u := by sorry
