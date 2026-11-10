-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_6
-- name    : HiddenHardCoreColoring.Mixing.lemma_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:05.722242+00:00
-- url     : https://prove2.me/theorems/6d7afd10-f314-4c6c-be2d-33162e207a3d
-- title:
--   Lemma 6 — the star operators sum to twice the heat-bath operators
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). For every vertex $v$,
--   $$\sum_{c\in[q]}Q_{v,c}=2Q_v\qquad\text{and}\qquad\sum_{c\in[q]}L_c=2L.$$
--
--   Every nontrivial recoloring at $v$ belongs to exactly the two stars centered at its old and new colors; this identity links the single-color operators to $L$.
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 6, p.10

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 6** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.10). For every vertex `v`, `∑_{c∈[q]} Q_{v,c} = 2Q_v`, and
`∑_{c∈[q]} L_c = 2L`. -/
theorem lemma_6 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) :
    (∀ v : V, ∑ c : Fin q, Qvc G q v c = (2 : ℝ) • Qv G q v) ∧
      ∑ c : Fin q, Lc G q c = (2 : ℝ) • Lap G q := by sorry

end HiddenHardCoreColoring.Mixing
