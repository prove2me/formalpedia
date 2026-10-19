-- Prove2me | Theorems.Thm_OAI_CrouzeixHilbert_Conformal_injOn_of_tendstoLocallyUniformlyOn
-- name    : OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:33:49.69044+00:00
-- url     : https://prove2.me/theorems/3afb68a7-2d6d-40a9-b93d-2f3bb500e8b6
-- title:
--   Hurwitz's theorem for injective functions: a nonconstant locally uniform limit of injective holomorphic functions on a connected open set is injective
-- statement:
--   Let $\iota$ be a type with a filter $l$ on it that is not the bottom filter (`[l.NeBot]`; for example $\iota = \mathbb N$ and $l$ = `atTop`). Let $U \subseteq \mathbb C$ be open (`IsOpen U`) and preconnected (`IsPreconnected U`). Let $F_i : \mathbb C \to \mathbb C$ ($i \in \iota$) and $f : \mathbb C \to \mathbb C$ be functions such that
--   - $F_i \to f$ locally uniformly on $U$ along $l$ (`TendstoLocallyUniformlyOn F f l U`);
--   - every $F_i$ is complex differentiable on $U$ (`DifferentiableOn ℂ (F i) U`);
--   - every $F_i$ is injective on $U$ (`InjOn (F i) U`); and
--   - $f$ is not constant on $U$: there is no $c \in \mathbb C$ with $f(z) = c$ for all $z \in U$.
--
--   Then $f$ is injective on $U$ (`InjOn f U`).
--
--   $$F_i \to f \text{ locally uniformly on } U,\quad F_i \text{ holomorphic and injective on } U,\quad f \not\equiv \text{const on } U \;\Longrightarrow\; f \text{ injective on } U.$$
--
--   This is the classical consequence of Hurwitz's theorem (A. Hurwitz, 1889) for injective functions, here for limits along an arbitrary nontrivial filter. The case of sequences ($l$ = `atTop` on $\mathbb N$) is already published and Proved as `OAI.DirectCrouzeix.Conformal.constant_or_injective_limit` (a876cd83).
--
--   Lean: `OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn`, OpenAI's theorem of that name (in `lean/OAI/Analysis/Crouzeix/Hurwitz.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   A. Hurwitz, Über die Nullstellen der Bessel'schen Function, Math. Ann. 33 (1889), 246–266 (Hurwitz's theorem on zeros of limits, of which this is the classical corollary for injective functions); proof and Lean code: OpenAI, The complete Crouzeix theorem: optimal similarity and a common positive boundary representation, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 325; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Crouzeix/Hurwitz.lean (declaration OAI.CrouzeixHilbert.Conformal.injOn_of_tendstoLocallyUniformlyOn)

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

theorem injOn_of_tendstoLocallyUniformlyOn {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : Set ℂ} (hU : IsOpen U) (hc : IsPreconnected U)
    {F : ι → ℂ → ℂ} {f : ℂ → ℂ} (hlim : TendstoLocallyUniformlyOn F f l U)
    (hd : ∀ i, DifferentiableOn ℂ (F i) U) (hi : ∀ i, InjOn (F i) U)
    (hnc : ¬ ∃ c, EqOn f (fun _ => c) U) : InjOn f U := by
  sorry

end CrouzeixHilbert.Conformal

end

end OAI
end
