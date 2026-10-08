-- Prove2me | Theorems.Thm_GivenDegreeSeq_GraphLimit_theorem_1_1
-- name    : GivenDegreeSeq.GraphLimit.theorem_1_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:59.933833+00:00
-- url     : https://prove2.me/theorems/a4a6d845-9ee0-45fd-8589-cabc07edb108
-- title:
--   Theorem 1.1 — uniform random graphs with degree scaling limit $f\in\operatorname{int}\mathcal F$ converge a.s. to $W(x,y)=e^{g(x)+g(y)}/(1+e^{g(x)+g(y)})$
-- statement:
--   For each $n$ let $d^n=(d^n_1,\dots,d^n_n)$ be a degree sequence of a simple graph on $n$ vertices, with $d^n_1\ge\dots\ge d^n_n$, and suppose that $\{d^n\}$ has scaling limit $f$ in the sense of (2). Suppose that $f$ belongs to the topological interior of the set $\mathcal F$ of scaling limits, in $D'[0,1]$ with the modified $L^1$ norm $\|\cdot\|_{1'}$. Then:
--
--   1. There is a function $g\in D'[0,1]$, unique on $[0,1]$, such that
--   $$W(x,y):=\frac{e^{g(x)+g(y)}}{1+e^{g(x)+g(y)}}\qquad\text{satisfies}\qquad f(x)=\int_0^1W(x,y)\,dy\quad\text{for all }x\in[0,1].$$
--   2. Let $g$ be such a function. For each $n$ let $G_n$ be a random graph chosen uniformly from the set of all simple graphs on $\{1,\dots,n\}$ with degree sequence $d^n$, all defined on one probability space. Then, almost surely, $G_n$ converges to the limit graph represented by $W$:
--   $$t(H,G_n)\longrightarrow t(H,W)\qquad\text{for every finite simple graph }H.$$
--
--   The theorem identifies the graph limit of a uniformly random dense graph with a prescribed degree sequence: it is the β-model graphon whose parameter function $g$ solves the continuum maximum-likelihood equation $f(x)=\int_0^1W(x,y)\,dy$.
--
--   **Formalization Note** Functions on $[0,1]$ are `ℝ → ℝ`; uniqueness of $g$ is equality on $[0,1]$. The paper does not specify how the $G_n$ for different $n$ are coupled; the statement quantifies over every probability space and every family of measurable $G_n$ with the prescribed marginal laws (an arbitrary joint law), which is the strongest reading. The almost-sure event is "for every $H$", with $H$ ranging over simple graphs on `Fin k` for all $k$. The second part is stated for every $g$ satisfying the first, which by uniqueness is the paper's $W$.
-- source:
--   Chatterjee, Diaconis & Sly, Random Graphs with a Given Degree Sequence, arXiv:1005.1136v5, pp. 4–5, Theorem 1.1

import Mathlib
import Definitions.Def_GivenDegreeSeq_Interior_DPrime
import Definitions.Def_GivenDegreeSeq_Interior_IsGraphic
import Definitions.Def_GivenDegreeSeq_Interior_ScalingLimit
import Definitions.Def_GivenDegreeSeq_GraphLimit_HomDensity
import Definitions.Def_GivenDegreeSeq_GraphLimit_EdgeModel

namespace GivenDegreeSeq.GraphLimit

open MeasureTheory

universe u

/-- **Theorem 1.1** (Chatterjee–Diaconis–Sly, arXiv:1005.1136v5, pp. 4–5). For each `n` let `dⁿ`
be a degree sequence of a simple graph on `n` vertices, written in nonincreasing order, and let
`f` be the scaling limit (2) of `{dⁿ}`. Suppose that `f` belongs to the topological interior of
`F` in `D′[0,1]` (modified `L¹` norm). Then

1. there is a function `g ∈ D′[0,1]`, unique on `[0,1]`, such that
   `W(x, y) := e^{g(x)+g(y)}/(1 + e^{g(x)+g(y)})` satisfies `f(x) = ∫₀¹ W(x, y) dy` for all
   `x ∈ [0,1]`; and
2. for any such `g`, if `G_n` is uniformly distributed on the simple graphs on `n` vertices with
   degree sequence `dⁿ` (for each `n`, all defined on one probability space, with an arbitrary
   joint law), then almost surely `G_n` converges to the graph limit represented by `W`:
   `t(H, G_n) → t(H, W)` for every finite simple graph `H`. -/
theorem theorem_1_1 (d : (n : ℕ) → Fin n → ℕ) (f : ℝ → ℝ)
    (hd : ∀ n, Antitone (d n) ∧ GivenDegreeSeq.Interior.IsGraphic (d n))
    (hf : GivenDegreeSeq.Interior.HasScalingLimit d f) (hint : GivenDegreeSeq.Interior.InteriorF f) :
    (∃ g : ℝ → ℝ, GivenDegreeSeq.Interior.InDprime g ∧ (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = ∫ y in (0 : ℝ)..1, Wg g x y) ∧
        ∀ h : ℝ → ℝ, GivenDegreeSeq.Interior.InDprime h →
          (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = ∫ y in (0 : ℝ)..1, Wg h x y) →
            Set.EqOn h g (Set.Icc 0 1)) ∧
      ∀ g : ℝ → ℝ, GivenDegreeSeq.Interior.InDprime g →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, f x = ∫ y in (0 : ℝ)..1, Wg g x y) →
          ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (Gs : (n : ℕ) → Ω → SimpleGraph (Fin n)),
            (∀ n, Measurable (Gs n)) →
            (∀ n, P.map (Gs n) = ProbabilityTheory.uniformOn (withDegrees (d n))) →
              ∀ᵐ ω ∂P, ConvergesTo (fun n => Gs n ω) (Wg g) := by sorry

end GivenDegreeSeq.GraphLimit
