-- Prove2me | Theorems.Thm_OPG37364_lps13Graph_connected_of_large
-- name    : OPG37364.lps13Graph_connected_of_large
-- status  : Proved
-- author  : @arexychen
-- created : 2026-09-12T14:10:26.548185+00:00
-- url     : https://prove2.me/theorems/8a9791a1-f249-4544-ab7f-194cc7ff39ed
-- title:
--   Connectedness of the fixed-13 LPS graph for sufficiently large primes
-- statement:
--   Let $q$ be a prime with $q>13^{60}$, and let $i\in\mathbb F_q$ satisfy $i^2=-1$. Suppose the Legendre symbol satisfies $(13/q)=-1$. Then the existing fixed-$13$ LPS Cayley graph on $\mathrm{PGL}_2(\mathbb F_q)$ is connected.
--   $$\operatorname{IsConnected}(\operatorname{lps13Graph}(q,i)).$$
--   The conclusion holds for every such choice of $i$. The deliberately coarse threshold suffices for subsequent existence arguments.
-- source:
--   Classical LPS/DSV connectedness, specialized to the existing fourteen norm-13 quaternion generators. Proof assembly uses the proved reduced-word separation bound and the prime-field metabelian consequence of Dickson classification. Original classification formalization: Qiuzhen-CFSG/CFSG, Apache-2.0, commit 96b2a02085dc678f3e0a97b334c31ada599c55fd, https://github.com/Qiuzhen-CFSG/CFSG/blob/96b2a02085dc678f3e0a97b334c31ada599c55fd/Glauberman/DicksonClassification.lean . arexychen contributes specialization, integration, target-environment replay and validation; no novelty claim for the classical mathematics.

import Definitions.Def_opg37364_lps13
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Tactic
set_option autoImplicit false

namespace OPG37364
theorem lps13Graph_connected_of_large
    {q : ℕ} [Fact q.Prime] (hqLarge : 13^60 < q)
    (i : LPS13Root q) (hnr : legendreSym q 13 = -1) :
    IsConnected (lps13Graph (show 13 < q by omega) i) := by sorry
end OPG37364
