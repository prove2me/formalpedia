-- Prove2me | Theorems.Thm_MartOT_Var_theorem_3_1
-- name    : MartOT.Var.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:10:34.598349+00:00
-- url     : https://prove2.me/theorems/0be16d52-a1f6-44fe-b881-410d99fea4ce
-- title:
--   Theorem 3.1, p. 17 — Kellerer's dichotomy: a Borel M ⊆ Zⁿ is covered by null cylinders or charged by a measure with marginals ≤ ζ
-- statement:
--   Let $Z$ be a Polish space with its Borel $\sigma$-algebra, $\zeta$ a Borel probability measure on $Z$, $n\in\mathbb N$, and $M\subseteq Z^n$ a Borel set. Write $\operatorname{proj}^i:Z^n\to Z$ for the $i$-th coordinate. Then (at least) one of the following holds:
--
--   1. there are subsets $M_1,\dots,M_n$ of $Z^n$ with $\zeta(\operatorname{proj}^i M_i)=0$ for $i=1,\dots,n$ and
--   $$M\subseteq\bigcup_{i=1}^n M_i;$$
--   2. there is a measure $\gamma$ on $Z^n$ with $\gamma(M)>0$ and $\operatorname{proj}^i_{\#}\gamma\le\zeta$ for $i=1,\dots,n$.
--
--   This is the form of Kellerer's duality theorem for multi-marginal problems given by Beiglböck, Goldstern, Maresch and Schachermayer (Proposition 2.1 of *Optimal and better transport plans*, 2009). In the proof of the variational lemma it is applied to $(Z,\zeta)=(\mathbb R^2,\pi)$ and the set of bad $n$-tuples.
--
--   **Formalization Note** The page says "$M\subseteq Z^n$"; the Lean statement assumes $M$ Borel, which is the case of the cited Proposition 2.1 and the only case the paper uses (its set $M$ is declared Borel on p. 17). The images $\operatorname{proj}^i M_i$ need not be Borel; $\zeta(\cdot)=0$ is then the outer measure, which is what "$\zeta$-null" means. "Either of the following holds" is read as an inclusive or.
-- source:
--   arXiv:1208.1509v2, Theorem 3.1, p. 17 (citing Beiglböck–Goldstern–Maresch–Schachermayer 2009, Proposition 2.1, and Kellerer 1984, Lemma 1.8(a), Corollary 2.18)

import Mathlib

namespace MartOT.Var

open MeasureTheory

theorem theorem_3_1 {Z : Type*} [TopologicalSpace Z] [PolishSpace Z] [MeasurableSpace Z]
    [BorelSpace Z] (ζ : Measure Z) [IsProbabilityMeasure ζ] (n : ℕ) (M : Set (Fin n → Z))
    (hM : MeasurableSet M) :
    (∃ Ms : Fin n → Set (Fin n → Z),
        (∀ i, ζ ((fun z : Fin n → Z => z i) '' Ms i) = 0) ∧ M ⊆ ⋃ i, Ms i) ∨
      (∃ γ : Measure (Fin n → Z), 0 < γ M ∧
        ∀ i, γ.map (fun z : Fin n → Z => z i) ≤ ζ) := by sorry

end MartOT.Var
