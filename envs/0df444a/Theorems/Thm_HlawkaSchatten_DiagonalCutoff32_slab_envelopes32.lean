-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_slab_envelopes32
-- name    : HlawkaSchatten.DiagonalCutoff32.slab_envelopes32
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:20:29.290819+00:00
-- url     : https://prove2.me/theorems/8364383b-c02d-413b-9dc5-d480d89e347e
-- title:
--   Slab envelope bounds on $[32,50]$
-- statement:
--   For every real exponent $p$ with $32\le p\le 50$,
--
--   $$\mathrm{scalarEnvelope}\big(p,q(p)\big)<K_p,$$
--
--   where $q(p)$ is the slab envelope radius (levels $0.3851,\dots,0.3730$ on the eight slabs of $[32,50]$) and $K_p$ is the cyclic constant.
--
--   This sharpens the uniform envelope level $0.386$ slab by slab, which shrinks the region where a normalized counterexample can lie.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_SlabRadius
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem HlawkaSchatten.DiagonalCutoff32.slab_envelopes32 : ∀ p : ℝ, 32 ≤ p → p ≤ 50 → scalarEnvelope p (slabRadius p) < cyclicConstant p := by sorry
