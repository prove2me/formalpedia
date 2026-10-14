-- Prove2me | Theorems.Thm_IntMul_HvdH_synG_lip
-- name    : IntMul.HvdH.synG_lip
-- status  : Proved
-- author  : @xuanji
-- created : 2026-10-12T01:29:48.940525+00:00
-- url     : https://prove2.me/theorems/c191fe2e-9887-4e5f-a042-fec02a1657a8
-- title:
--   The normalised synthetic FFT is 1-Lipschitz
-- statement:
--   For $R=\mathbb C[y]/(y^r+1)$ and $t=2^e$, the normalised synthetic transform $\mathcal G_t=\tfrac1t\,\widehat{\cdot}$, computed by the radix-2 recursion `synG`, is $1$-Lipschitz for the sup norm on coefficient arrays:
--   $$\|\mathcal G_t u-\mathcal G_t v\|_\infty\le\|u-v\|_\infty.$$
--   This is the norm bound $\|\mathcal G_t\|\le1$ used in Harvey–van der Hoeven §3.2.
-- source:
--   Harvey, van der Hoeven, Integer multiplication in time O(n log n), Annals of Math. 193 (2021), https://hal.science/hal-02070778, Lemma 3.2

import Definitions.Def_IntMul_HvdH_SynFFT

namespace IntMul.HvdH
theorem synG_lip (r e : ℕ) : SupLip (synG r e) := by sorry
end IntMul.HvdH
