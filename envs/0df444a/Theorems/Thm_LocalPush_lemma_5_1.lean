-- Prove2me | Theorems.Thm_LocalPush_lemma_5_1
-- name    : LocalPush.lemma_5_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:23.554533+00:00
-- url     : https://prove2.me/theorems/2277af21-df82-42d8-a13c-8c843e9daa56
-- title:
--   Lemma 5.1 — expanding the active set increases the exact state: $x^{(S\cup T)}\ge x^{(S)}$ and (12)
-- statement:
--   Let $G$ be a finite simple graph without isolated nodes, $\alpha\in(0,1)$ and $\lambda>0$. Suppose $s\in S\subseteq V$ and $T\subseteq\partial S$ satisfies $r(x^{(S)})(v)>\lambda d(v)$ for every $v\in T$. Then $x^{(S\cup T)}\ge x^{(S)}$ entrywise, and
--   $$x^{(S\cup T)}(v)\ \ge\ \frac{\alpha}{d(v)}\Big(r\big(x^{(S)}\big)(v)-\lambda d(v)\Big)\qquad\forall v\in T.\tag{12}$$
--
--   This monotonicity is the induction step for the nonnegativity and lower bounds of Lemma 5.3, and (12) gives the lower bound (20) on the decrease of the potential.
--
--   Differences from the source: none.
-- source:
--   Cui, Wei, Yang, Revisiting Local Push, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.1, p.18 (PDF p.18)

import Mathlib
import Definitions.Def_LocalPush_ResidueSystem

open Finset Matrix

namespace LocalPush

/-- **Lemma 5.1 (monotonicity of the exact states under expansion).**

Cui, Wei, Yang, *Revisiting Local Push: Faster Algorithms and Optimal Query Complexity for PageRank and
Effective Resistance*, STOC 2027 submission (manuscript sha256 4c36279a…), §5.1, Lemma 5.1, p.18 (PDF p.18).

"Suppose s ∈ 𝒮 ⊆ V and 𝒯 ⊆ ∂𝒮 satisfies r(x^(𝒮))_𝒯 > λd_𝒯. Then x^(𝒮∪𝒯) ≥ x^(𝒮) and
x^(𝒮∪𝒯)(v) ≥ (α/d(v))(r(x^(𝒮))(v) − λd(v)), ∀ v ∈ 𝒯. (12)"

On a simple graph without isolated nodes, with `α ∈ (0, 1)` and the internal threshold `λ > 0` of
Algorithm 3: if `s ∈ S` and `T ⊆ ∂S` with `r(x^(S))(v) > λd(v)` for every `v ∈ T`, then `x^(S∪T) ≥ x^(S)`
entrywise and (12) holds on `T`. Here `x^(S)` is eq. (11) and `r` is eq. (8). -/
theorem lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : NoIsolated G) (s : V) (α lam : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hlam : 0 < lam)
    (S T : Finset V) (hs : s ∈ S) (hT : T ⊆ bdry G S)
    (hr : ∀ v ∈ T, lam * deg G v < resid G α s (xS G s α lam S) v) :
    (∀ v, xS G s α lam S v ≤ xS G s α lam (S ∪ T) v) ∧
      ∀ v ∈ T, α / deg G v * (resid G α s (xS G s α lam S) v - lam * deg G v) ≤
        xS G s α lam (S ∪ T) v := by sorry

end LocalPush
