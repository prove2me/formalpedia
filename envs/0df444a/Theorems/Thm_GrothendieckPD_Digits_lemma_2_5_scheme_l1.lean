-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_5_scheme_l1
-- name    : GrothendieckPD.Digits.lemma_2_5_scheme_l1
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T02:49:23.583661+00:00
-- url     : https://prove2.me/theorems/6e1abecf-ab4c-42d4-8245-309f5ed47004
-- title:
--   Lemma 2.5, mixed schemes: $\sum_m |c_m(\mu)|\le 1$
-- statement:
--   Let $\mu$ be a distribution on pairs of measurable sign functions $f,g:\mathbb R^n\to\{\pm1\}$, and let
--   $$c_m(\mu)=\mathbb E_{(f,g)\sim\mu}\,c_m(f,g)$$
--   be its averaged degree-$m$ Hermite coefficient. Then
--   $$\sum_{m=0}^{\infty}|c_m(\mu)|\le 1,$$
--   and the series of absolute values is summable. This is the mixed-scheme estimate in the proof of Lemma 2.5, obtained by averaging the corresponding pair estimate and using $\mathbb E\,\sum_m|c_m(f,g)|\le1$.
--
--   **Formalization Note** The distribution is represented by the published jointly measurable random-pair structure `GrothendieckLB.MixedScheme`, over an arbitrary probability space; no oddness assumption is needed. The average is the Bochner integral `schemeCoeff`. Explicit summability makes the bound a genuine $\ell^1$ norm estimate.
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.5 and its proof, p. 5

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames
open MeasureTheory Filter

namespace GrothendieckPD.Digits

/-- The mixed-scheme coefficient estimate in Lemma 2.5 (p. 5): for a distribution on
pairs of measurable sign functions, the averaged Hermite coefficients are absolutely
summable and their absolute sum is at most one. -/
theorem lemma_2_5_scheme_l1 :
    ∀ (n : ℕ) (S : GrothendieckLB.MixedScheme n),
      (Summable fun m => |schemeCoeff S m|) ∧ (∑' m, |schemeCoeff S m| ≤ 1) := by sorry
