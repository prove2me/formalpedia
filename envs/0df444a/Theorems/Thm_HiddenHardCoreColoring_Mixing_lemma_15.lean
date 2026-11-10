-- Prove2me | Theorems.Thm_HiddenHardCoreColoring_Mixing_lemma_15
-- name    : HiddenHardCoreColoring.Mixing.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T09:00:03.463691+00:00
-- url     : https://prove2.me/theorems/fc8920dc-9ec3-4296-9b82-7875e8637c01
-- title:
--   Lemma 15 — ∑_c M_c(f) ≥ ⟨f, Lf⟩ and ∑_c V_c(f) ≤ ⟨f, Lf⟩
-- statement:
--   Throughout, $G=(V,E)$ is a finite simple graph on $n=|V|\ge1$ vertices with $\deg(v)\le\Delta$ for every $v$, $[q]=\{0,\dots,q-1\}$ is the palette, $\Omega$ is the set of proper $q$-colorings, $\mu$ is uniform on $\Omega$, and $q\ge\Delta+3$ (the standing assumption of §§3.2–7). For every $f\in L^2(\mu)$,
--   $$\sum_{c\in[q]}M_c(f)\ge\langle f,Lf\rangle_\mu\qquad\text{and}\qquad\sum_{c\in[q]}V_c(f)\le\langle f,Lf\rangle_\mu .$$
--
--   After summing over colors the mean parts alone control the Dirichlet form.
--
--   **Formalization Note** Functions on $\Omega$ are all real functions on the subtype of proper colorings; operators are matrices on $\Omega$ acting by $(Mf)(\sigma)=\sum_\tau M(\sigma,\tau)f(\tau)$, and $\langle f,g\rangle_\mu$ is the uniformly weighted sum.
--
--   Differences from the source: none.
-- source:
--   Xiongxin Yang, Glauber Dynamics for Sampling Colorings: Rapid Mixing above (1 + 1/e)Δ via Hidden Hard-Core Models, STOC 2027 submission #964 (October 2026), source.pdf sha256 3affe7a3f185d03ac2add85053eb4b8cb6cade88b65c789fb1b595ad6c177146; printed page = PDF page; Lemma 15, p.17

import Mathlib
import Definitions.Def_HiddenHardCoreColoring_Mixing_Coloring

open Finset Matrix

namespace HiddenHardCoreColoring.Mixing

/-- **Lemma 15** (Xiongxin Yang, STOC 2027 submission #964 (October 2026), p.17). For every `f`, `∑_c M_c(f) ≥ ⟨f, Lf⟩_µ` and `∑_c V_c(f) ≤ ⟨f, Lf⟩_µ`. -/
theorem lemma_15 {V : Type} [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (Δ q : ℕ) (hdeg : ∀ v, G.degree v ≤ Δ) (hq : Δ + 3 ≤ q) (f : Col G q → ℝ) :
    ip G q f (Lap G q *ᵥ f) ≤ ∑ c : Fin q, Mc G q c f ∧
      ∑ c : Fin q, Vc G q c f ≤ ip G q f (Lap G q *ᵥ f) := by sorry

end HiddenHardCoreColoring.Mixing
