-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_zero_or_ne_of_tendstoLocallyUniformlyOn
-- name    : OAI.CrouzeixHilbert.Conformal.zero_or_ne_of_tendstoLocallyUniformlyOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:33:50.830373+00:00
-- url     : https://prove2.me/theorems/8fc428b9-84dc-4976-8c1c-c14146c56306
-- title:
--   Hurwitz's theorem: a locally uniform limit of zero-free holomorphic functions on a connected open set is identically zero or zero-free
-- statement:
--   Let $\iota$ be a type with a filter $l$ on it that is not the bottom filter (`[l.NeBot]`; for example $\iota = \mathbb N$ and $l$ = `atTop`). Let $U \subseteq \mathbb C$ be open (`IsOpen U`) and preconnected (`IsPreconnected U`). Let $F_i : \mathbb C \to \mathbb C$ ($i \in \iota$) and $f : \mathbb C \to \mathbb C$ be functions such that
--   - $F_i \to f$ locally uniformly on $U$ along $l$ (`TendstoLocallyUniformlyOn F f l U`);
--   - every $F_i$ is complex differentiable on $U$ (`DifferentiableOn ℂ (F i) U`); and
--   - no $F_i$ vanishes on $U$: $F_i(z) \ne 0$ for all $i$ and all $z \in U$.
--
--   Then either $f$ is identically zero on $U$ (`EqOn f 0 U`) or $f$ has no zero in $U$.
--
--   $$F_i \to f \text{ locally uniformly on } U,\quad F_i \text{ holomorphic and zero-free on } U \;\Longrightarrow\; f \equiv 0 \text{ on } U \ \text{ or } \ f(z) \ne 0 \ \ \forall z \in U.$$
--
--   This is Hurwitz's theorem on the zeros of limits (A. Hurwitz, 1889), here for limits along an arbitrary nontrivial filter.
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.zero_or_ne_of_tendstoLocallyUniformlyOn`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/Hurwitz.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle. Forms of Hurwitz's theorem for sequences are already published and Proved on this platform: `OAI.DirectCrouzeix.Conformal.zero_or_nonvanishing_limit` (c2c36f3f), the case $l$ = `atTop` on $\mathbb N$ of this statement; `AhlforsComplexAnalysis.hurwitz` (697a8f15), for sequences of analytic functions converging uniformly on compact subsets of a region; and `hurwitz_nonvanishing_limit` (62b01429), for sequences converging uniformly on all of $U$. This statement allows limits along any nontrivial filter.
-- source:
--   A. Hurwitz, Über die Nullstellen der Bessel'schen Function, Math. Ann. 33 (1889), 246–266 (the theorem); proof and Lean code: OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/Hurwitz.lean (declaration OAI.CrouzeixHilbert.Conformal.zero_or_ne_of_tendstoLocallyUniformlyOn)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem zero_or_ne_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U)
    (hz : ∀ i z, z ∈ U → F i z ≠ 0) :
    EqOn f 0 U ∨ ∀ z ∈ U, f z ≠ 0 := by
  sorry

end CrouzeixHilbert.Conformal

end

end OAI
end
