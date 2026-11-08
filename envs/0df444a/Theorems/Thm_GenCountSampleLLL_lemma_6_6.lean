-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_6
-- name    : GenCountSampleLLL.lemma_6_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:56:46.168076+00:00
-- url     : https://prove2.me/theorems/21da17e7-4a44-4fd8-89e9-251a6068ffc4
-- title:
--   Lemma 6.6, pp.25–26 — a signed flow with $\partial\varphi=\mu^--\mu^+$ and energy $\le(6/(1-c)+mx_a)/Z_-$
-- statement:
--   Assume (1.1) with $c=1/100$ for some $x\in(0,1)^{\mathcal C}$, let $m=|\mathcal C|$, $a\in\mathcal D\subseteq\mathcal C$, $Z_-=Z_{\mathcal D^-}$. There is a signed flow $\varphi$ on the edges of $P=P_{\mathcal D,a}$ (an antisymmetric function of ordered pairs of states, zero off the edges) with divergence $\partial\varphi=\mu^--\mu^+$ and
--   $$
--   \sum_{\{X,Y\}}\frac{\varphi(X,Y)^2}{\mathrm{cap}(X,Y)}\le\frac{6/(1-c)+m\,x_a}{Z_-},
--   $$
--   the sum running over edges, each counted once.
--
--   With Lemma 6.4 this bounds $\|(\mu^--\mu^+)K^N\|_{\mathrm{TV}}$.
--
--   Differences from the source:
--   - encoding: the standing assumption of §2, p.7: "Throughout the proof, we assume (1.1) with c = 1/100", with x ∈ (0,1)^𝒞 → explicit hypotheses `hx : ∀ b, 0 < x b ∧ x b < 1` and `hLLL : I.LLLCond (1/100) x`; reason: the statement on the page omits the section's standing assumption; the Lean states it
--   - encoding: a signed flow on oriented edges, ∂φ(X) = Σ_{Y:{X,Y} edge} φ(X,Y), energy over unordered edges → φ on all ordered pairs, antisymmetric and zero off the edges; divergence Σ_Y φ(X,Y); energy ½ Σ_{X,Y edge} φ²/cap; reason: the same quantities
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, arXiv:2609.23671 (held file sha256 cd449f83…), Lemma 6.6, pp.25–26

import Mathlib
import Definitions.Def_GenCountSampleLLL_Inst
import Definitions.Def_GenCountSampleLLL_twoTrees
import Definitions.Def_GenCountSampleLLL_insertionChain

set_option autoImplicit false

open scoped BigOperators ENNReal

open Classical

namespace GenCountSampleLLL

open Inst

/-- Lemma 6.6, pp.25–26 (Jain, Mizgerd, Pham, *A general counting and sampling Lovász local lemma*, arXiv:2609.23671 (held file sha256 cd449f83…)), under (1.1) with `c = 1/100`. For `a ∈ D ⊆ C` there
is a signed flow `φ` on the edges of `P = P_{D,a}` with `∂φ = µ⁻ − µ⁺` and
`Σ_{{X,Y}} φ(X,Y)²/cap(X,Y) ≤ (6/(1 − c) + m x_a)/Z₋`, with `Z₋ = Z_{D⁻}`.

**Formalization Note.** A signed flow is an antisymmetric function on ordered pairs of states,
zero off the edges (an edge is a pair of distinct states with `P(X,Y) > 0`); its divergence at `X`
is `Σ_Y φ(X,Y)`. The energy counts each unordered edge once, written as one half of the sum over
ordered pairs. -/
theorem lemma_6_6 (I : Inst) (x : Fin I.m → ℝ) (hx : ∀ b, 0 < x b ∧ x b < 1)
    (hLLL : I.LLLCond (1 / 100) x) (D : Finset (Fin I.m)) (a : Fin I.m) (ha : a ∈ D) :
    ∃ φ : I.S D a → I.S D a → ℝ,
      (∀ X Y, φ Y X = -φ X Y) ∧ (∀ X Y, ¬ I.IsEdge D a X Y → φ X Y = 0) ∧
      (∀ X, ∑ Y, φ X Y = I.muMinus D a X - I.muPlus D a X) ∧
      1 / 2 * ∑ X, ∑ Y, (if I.IsEdge D a X Y then φ X Y ^ 2 / I.cap D a X Y else 0) ≤
        (6 / (1 - 1 / 100) + (I.m : ℝ) * x a) / I.Z (D.erase a) := by sorry

end GenCountSampleLLL
