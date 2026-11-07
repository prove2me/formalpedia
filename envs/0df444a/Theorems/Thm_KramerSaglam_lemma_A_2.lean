-- Prove2me | Theorems.Thm_KramerSaglam_lemma_A_2
-- name    : KramerSaglam.lemma_A_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:05:55.676205+00:00
-- url     : https://prove2.me/theorems/18828123-d82a-4361-b295-c19636871cf6
-- title:
--   Lemma A.2 — the comparison function $F_\rho$ and the bounds $I(B:C)\le V$, $|d|\le V$
-- statement:
--   Let $A,B$ be unbiased bits with absolute correlation $\rho$, and let $C$ be a nonconstant bit such that $A-B-C$ is a Markov chain. Write $V=\bar H(C)$, $d=\mathbb E[(2B-1)(2C-1)]$ and $f(t)=D_2\big(\tfrac{1+t}2\,\|\,\tfrac12\big)$, and define $F_\rho$ on $[0,1]$ by $F_\rho(f(t))=f(\rho t)$ for $0\le t\le1$. Then $F_\rho$ is increasing and concave on $[0,1]$, and
--   $$
--   I(B:C)\le V,\qquad I(A:C)\le V\,F_\rho\Big(\frac{I(B:C)}{V}\Big),\qquad |d|\le V,\qquad I(B:C)\ge V f(d/V).
--   $$
--
--   This is the comparison behind Lemma 3.4 (via Jensen's inequality for the concave $F_\rho$) and Lemma 3.5.
--
--   **Formalization Note** The chain is given by its channel $p=P(A\ne B)$, so $\rho=|1-2p|$; every $\rho\in[0,1]$ arises. $F_\rho$ is any function with the defining property; since $f$ maps $[0,1]$ bijectively onto $[0,1]$, this fixes $F_\rho$ on $[0,1]$.
--
--   Differences from the source:
--   - reading: "increasing" → monotone (non-decreasing) on [0, 1]; reason: the paper writes "strictly increasing" when it means that (f, same page), and at ρ = 0, a case the proof covers, F_ρ is constant
--   - encoding: F_ρ defined by F_ρ(f(t)) = f(ρt) → any F satisfying F(f(t)) = f(ρt) for t ∈ [0, 1]; reason: f is a bijection of [0, 1], so this is the same function there and avoids an inverse
--   - encoding: unbiased bits with absolute correlation ρ → a chain with P(A △ B) = p and ρ = |1 − 2p|; reason: for unbiased bits E[(2A−1)(2B−1)] = 1 − 2p
-- source:
--   Kramer, Saglam, On the most informative Boolean function under noise, arXiv:2611.05430 (held copy sha256 d787ef8d…), Lemma A.2 and the setup before it, p.13

import Mathlib
import Definitions.Def_KramerSaglam_Scalars
import Definitions.Def_KramerSaglam_Conditional
import Definitions.Def_KramerSaglam_Model
import Definitions.Def_KramerSaglam_PairSetup

open MeasureTheory

namespace KramerSaglam

/-- **Lemma A.2.** D. Kramer, M. Saglam, *On the most informative Boolean function under noise*, arXiv:2611.05430 (held copy sha256 d787ef8d…), p.13. `A`, `B` are unbiased bits with absolute correlation `ρ = |1 − 2p|`, `C` is a nonconstant
bit with `A − B − C` a Markov chain, `V = H̄(C)`, `d = E[(2B − 1)(2C − 1)]`, and `F_ρ` is given by `F_ρ(f(t)) = f(ρt)` on `[0, 1]`.

**Formalization Note.** `F` is any function with the defining property. `f` is a bijection of `[0, 1]`, so this fixes `F` on `[0, 1]`,
with no junk value from an inverse. "Increasing" is `MonotoneOn`: the paper writes "strictly increasing" when it means that, and at
`ρ = 0` the function is constant. -/
theorem lemma_A_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (A B C : Set Ω) (h : IsChain P p A B C) (hpos : 0 < P.real C) (hlt : P.real C < 1)
    (F : ℝ → ℝ) (hF : ∀ t ∈ Set.Icc (0 : ℝ) 1, F (f t) = f (|1 - 2 * p| * t)) :
    MonotoneOn F (Set.Icc 0 1) ∧ ConcaveOn ℝ (Set.Icc 0 1) F ∧
      info P B (sigma C) ⊥ ≤ tsGiven P C ⊥ ∧
      info P A (sigma C) ⊥ ≤ tsGiven P C ⊥ * F (info P B (sigma C) ⊥ / tsGiven P C ⊥) ∧
      |bitCorr P B C| ≤ tsGiven P C ⊥ ∧
      info P B (sigma C) ⊥ ≥ tsGiven P C ⊥ * f (bitCorr P B C / tsGiven P C ⊥) := by sorry

end KramerSaglam
