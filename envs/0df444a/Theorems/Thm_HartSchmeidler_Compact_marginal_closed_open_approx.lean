-- Prove2me | Theorems.Thm_HartSchmeidler_Compact_marginal_closed_open_approx
-- name    : HartSchmeidler.Compact.marginal_closed_open_approx
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:14:06.718329+00:00
-- url     : https://prove2.me/theorems/e79b1fec-7035-4100-b4e5-5836518500cd
-- title:
--   Proof of Theorem 3, p. 24 and footnote 16 — the marginal of a regular measure on a compact product is regular
-- statement:
--   Let each $S^i$ be a compact Hausdorff space with its Borel σ-algebra $\Sigma^i$, and let $p$ be a regular probability measure on $S=\prod_jS^j$ with the product topology and its Borel σ-algebra. Fix a player $i$, a Borel set $R^i\subseteq S^i$ and $\varepsilon>0$. Then there are a closed set $F^i$ and an open set $G^i$ in $S^i$ with $F^i\subseteq R^i\subseteq G^i$ and
--   $$
--   p\bigl((G^i\setminus F^i)\times S^{-i}\bigr)<\varepsilon .
--   $$
--
--   In the paper's words (footnote 16): "in a compact space, the marginal of a regular measure is also regular." This lets the special case of the proof replace the discontinuous deviation by a continuous one, up to an error of measure less than $\varepsilon$.
--
--   **Formalization Note** $(G^i\setminus F^i)\times S^{-i}$ is the set of profiles $s$ with $s^i\in G^i\setminus F^i$. The page writes the set $R^i\times S^{-i}$ with the $i$-th factor first; it is the set $\{s: s^i\in R^i\}$.
-- source:
--   Hart and Schmeidler, Existence of Correlated Equilibria, Math. Oper. Res. 14 (1989), p. 24, proof of Theorem 3, special case ("The measure p is regular; therefore there exist sets F, G ⊂ S") and footnote 16; https://doi.org/10.1287/moor.14.1.18

import Definitions.Def_HartSchmeidler_Compact_Game

namespace HartSchmeidler.Compact

open MeasureTheory

/-- Proof of Theorem 3, p. 24, with footnote 16: for a regular probability measure `p` on the
compact space `S`, every Borel set `Rⁱ ⊆ Sⁱ` lies between a closed `Fⁱ` and an open `Gⁱ` with
`p((Gⁱ \ Fⁱ) × S⁻ⁱ) < ε`. -/
theorem marginal_closed_open_approx {ι : Type*} {S : ι → Type*}
    [∀ i, TopologicalSpace (S i)] [∀ i, CompactSpace (S i)] [∀ i, T2Space (S i)]
    [∀ i, MeasurableSpace (S i)] [∀ i, BorelSpace (S i)]
    (p : Measure (Profile S)) [IsProbabilityMeasure p] (hp : p.Regular)
    (i : ι) (R : Set (S i)) (hR : MeasurableSet R) (ε : ℝ) (hε : 0 < ε) :
    ∃ F G : Set (S i), IsClosed F ∧ IsOpen G ∧ F ⊆ R ∧ R ⊆ G ∧
      p ((fun s : Profile S => s i) ⁻¹' (G \ F)) < ENNReal.ofReal ε := by sorry

end HartSchmeidler.Compact
