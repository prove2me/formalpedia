-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff32_envelope_certificate_sound
-- name    : HlawkaSchatten.DiagonalCutoff32.envelope_certificate_sound
-- status  : Proved
-- author  : @@bwdaugherty
-- created : 2026-10-16T14:19:50.618312+00:00
-- url     : https://prove2.me/theorems/064193fe-17bd-4bee-95dd-4367c73750a0
-- title:
--   Polynomial certificates imply the scalar envelope bound
-- statement:
--   Soundness of the slab envelope certificate. Let $32\le a\le p\le b\le 50$, $n>0$ with $a\le n$, $\ell\ge 1$ with $\log n\le \ell$ and $(\ell-1)/32+1/a\le 1/5$, and $0<q\le 2/5$. Suppose that for every $x\in[1/b,1/a]$
--
--   $$(1-q)\,\mathrm{DupG}(a/n,x)<\mathrm{NloG}(a/n,\ell-1,1/a,x)\cdot 2\,\mathrm{GloG}(x).$$
--
--   Then $\mathrm{scalarEnvelope}(p,q)<K_p$, where $K_p$ is the cyclic constant.
--
--   The hypothesis is a one-variable polynomial inequality on an interval, so each slab of exponents reduces to a finite polynomial check; the witness $t=(a/(n p))^{1/p}$ is used for the cyclic ratio.
-- source:
--   Sharp diagonal Hlawka constant campaign, cutoff-32 entry (https://prove2.me/campaigns/sharp-diagonal-hlawka-constant); definitions of the foundation mission (Ezzeri Esa, Apache-2.0).

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalCutoff32_EnvelopeBounds
import Mathlib

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction
open HlawkaSchatten.DiagonalCutoff32

theorem HlawkaSchatten.DiagonalCutoff32.envelope_certificate_sound : ∀ a b n ℓ q p : ℝ, 32 ≤ a → b ≤ 50 → 0 < n → a ≤ n →
    Real.log n ≤ ℓ → 1 ≤ ℓ → (ℓ - 1) * (1/32) + 1/a ≤ 1/5 → 0 < q → q ≤ 2/5 →
    (∀ x : ℝ, 1/b ≤ x → x ≤ 1/a →
      (1 - q) * DupG (a/n) x < NloG (a/n) (ℓ - 1) (1/a) x * (2 * GloG x)) →
    a ≤ p → p ≤ b → scalarEnvelope p q < cyclicConstant p := by sorry
